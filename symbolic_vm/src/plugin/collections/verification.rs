use move_core_types::{
  identifier::Identifier,
  vm_status::{StatusCode, VMStatus},
};

use vm::{
  errors::*,
  file_format::SignatureToken,
};

use crate::{
  plugin::Plugin,
  runtime::{
    interpreter::SymInterpreter,
    loader::{Loader, Function},
  },
  state::{
    vm_context::SymbolicVMContext,
  },
  types::values::{SymBool, SymValue, SymbolicMoveValue},
};

use move_vm_types::loaded_data::runtime_types::Type;

use std::{
  collections::{HashMap, HashSet, VecDeque},
  convert::TryInto,
  iter::FromIterator,
};

use z3::{
  ast::{Ast, Bool, Dynamic, exists_const},
  Context,
  Goal,
  Solver,
  SatResult,
  Tactic,
};
use z3_sys::AstKind;

pub struct Specification<'a, 'ctx> {
  pre: Box<dyn Fn(&[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
  post: Box<dyn Fn(&[SymValue<'ctx>], &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
  abort: Box<dyn Fn(&[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
}

impl<'a, 'ctx> Specification<'a, 'ctx> {
  pub fn new(
    pre: impl Fn(&[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
    post: impl Fn(&[SymValue<'ctx>], &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
    abort: impl Fn(&[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
  ) -> Self {
    Self {
      pre: Box::new(pre),
      post: Box::new(post),
      abort: Box::new(abort),
    }
  }

  pub fn pre(&self, args: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.pre)(args)
  }

  pub fn post(&self, args: &[SymValue<'ctx>], returns: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.post)(args, returns)
  }

  pub fn abort(&self, args: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.abort)(args)
  }
}

pub struct VerificationPlugin<'a, 'ctx> {
  z3_ctx: &'ctx Context,
  target: Specification<'a, 'ctx>,
  specs: HashMap<Identifier, Specification<'a, 'ctx>>,
}

impl<'a, 'ctx> VerificationPlugin<'a, 'ctx> {
  pub fn new(z3_ctx: &'ctx Context, target: Specification<'a, 'ctx>) -> Self {
    Self {
      z3_ctx,
      target,
      specs: HashMap::new(),
    }
  }

  pub fn add_spec(&mut self, func_name: Identifier, spec: Specification<'a, 'ctx>) {
    self.specs.insert(func_name, spec);
  }
}

impl<'a, 'ctx> Plugin<'ctx> for VerificationPlugin<'a, 'ctx> {
  fn on_before_call<'vtxn>(
    &self,
    _vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    _loader: &Loader,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    func: &Function,
    _ty_args: Vec<Type>,
  ) -> PartialVMResult<bool> {
    match self.specs.get(&Identifier::new(func.name()).unwrap())  {
      Some(spec) => {
        let z3_ctx = interpreter.state.get_z3_ctx();
        let solver = &interpreter.solver;
        let arg_count = func.arg_count();
        let args = interpreter.operand_stack.popn(arg_count.try_into().unwrap())?;
        solver.push();
        solver.assert(&spec.pre(args.as_slice()).as_inner().not());
        if solver.check() == SatResult::Sat {
          println!("precondition may not be satisfied! should abort now!");
        }
        solver.pop(1);
        let mut returns = vec![];
        let mut prefix = String::from(func.name());
        prefix.push_str("!return");
        // TODO: should consider generics, substitude ty_args
        // TODO: also model other type of returns
        for sig in &func.returns().0 {
          let val = match sig {
            SignatureToken::Bool => SymValue::new_bool(z3_ctx, &prefix),
            SignatureToken::U8 => SymValue::new_u8(z3_ctx, &prefix),
            SignatureToken::U64 => SymValue::new_u64(z3_ctx, &prefix),
            SignatureToken::U128 => SymValue::new_u128(z3_ctx, &prefix),
            _ => unimplemented!(),
          };
          returns.push(val);
        }
        let post_cond = spec.post(args.as_slice(), returns.as_slice());
        solver.assert(post_cond.as_inner());
        // TODO: consider if at here solver is unsat
        interpreter.spec_conditions.push((args, post_cond));
        for val in returns {
          interpreter.operand_stack.push(val)?;
        }
        Ok(true)
      }
      None => Ok(false)
    }
  }

  // fn on_after_call capture the return value

  fn on_after_execute<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    // args: &[SymValue<'ctx>],
    return_values: &[SymValue<'ctx>],
  ) -> PartialVMResult<()> {
    interpreter.solver.push();
    interpreter.solver.assert(self.target.post(&[], return_values).as_inner()); // TODO: args should not be empty!!
    if interpreter.solver.check() == SatResult::Sat {
      interpreter.solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!("Post condition meet in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    println!("-------VERIFICATION BEGIN-------");
    println!("Counter example found! See SUGGESTION and REPORT section.");
    println!("-------VERIFICATION END---------");
    interpreter.solver.pop(1);
    let pc = Bool::and(self.context,
      &interpreter.path_conditions.iter()
        .chain(interpreter.spec_conditions.iter().map(|(_, s)| s)).map(|v| v.as_inner())
        .collect::<Vec<_>>());
    for (spec_inputs, spec) in interpreter.spec_conditions.iter() {
      let spec_vars = collect_variables(spec.as_inner());
      let solver = Solver::new(self.context);
      let projected = project(self.context, &pc, &spec_vars).expect("Quantifier Elimination Failed!");
      let phi = spec.as_inner();
      solver.assert(phi);
      solver.assert(&projected.not());
      match solver.check() {
        SatResult::Sat => {
          let inputs = HashSet::from_iter(spec_inputs.iter().map(|v| v.as_ast().unwrap()));
          let projected_input = project(self.context, &pc, &inputs).expect("Quantifier Elimination Failed!");
          let suggested = Bool::and(self.context, &[
            &projected_input.implies(&Bool::and(self.context, &[&projected.not(), phi]).simplify()),
            &projected_input.not().implies(phi)]);
          println!("-------SUGGESTION BEGIN-------");
          println!("previous condition:");
          println!("{:#?}", phi);
          println!("suggested condition:");
          println!("{:#?}", suggested);
          println!("-------SUGGESTION END---------");
        },
        _ => {}
      }
    }
    Ok(())
  }
}

fn collect_variables<'ctx>(var: &impl Ast<'ctx>) -> HashSet<Dynamic<'ctx>> {
  let mut queue: VecDeque<Dynamic<'ctx>> = VecDeque::new();
  let mut result = HashSet::new();
  queue.push_back(Dynamic::from_ast(var));
  loop {
    match queue.pop_front() {
      Some(v) => if AstKind::App == v.kind() && v.children().len() == 0 {
        result.insert(v);
      } else {
        queue.append(&mut VecDeque::from(v.children()));
      },
      None => break,
    }
  }
  return result;
}

fn project<'ctx>(ctx: &'ctx Context, cond: &Bool<'ctx>, vars: &HashSet<Dynamic<'ctx>>) -> Option<Bool<'ctx>> {
  let tactic = Tactic::new(ctx, "qe"); //.and_then(&Tactic::new(ctx, "simplify"));
  let goal = Goal::new(ctx, false, false, false);
  let bounds = collect_variables(cond);
  let bounds = bounds.difference(vars).collect::<Vec<_>>();
  goal.assert(&exists_const(ctx, &bounds, &[], cond));
  let result = tactic.apply(&goal, None)
    .list_subgoals().collect::<Vec<Goal>>();
  result.first().map(|g| Bool::and(ctx, &g.get_formulas::<Bool<'ctx>>().iter().collect::<Vec<_>>()))
}