use move_core_types::{
  identifier::Identifier,
};

use vm::{
  errors::*,
  file_format::SignatureToken,
};

use crate::{
  plugin::{Plugin, PluginContext},
  runtime::{
    loader::{Loader, Function},
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

pub struct Specification<'a> {
  pre: Box<dyn for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
  post: Box<dyn for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>], &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
  abort: Box<dyn for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a>,
}

impl<'a> Specification<'a> {
  pub fn new(
    pre: impl for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
    post: impl for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>], &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
    abort: impl for<'ctx> Fn(&'ctx Context, &[SymValue<'ctx>]) -> SymBool<'ctx> + 'a,
  ) -> Self {
    Self {
      pre: Box::new(pre),
      post: Box::new(post),
      abort: Box::new(abort),
    }
  }

  pub fn pre<'ctx>(&self, z3_ctx: &'ctx Context, args: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.pre)(z3_ctx, args)
  }

  pub fn post<'ctx>(&self, z3_ctx: &'ctx Context, args: &[SymValue<'ctx>], returns: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.post)(z3_ctx, args, returns)
  }

  pub fn abort<'ctx>(&self, z3_ctx: &'ctx Context, args: &[SymValue<'ctx>]) -> SymBool<'ctx> {
    (self.abort)(z3_ctx, args)
  }
}

pub struct VerificationPlugin<'a> {
  target: Specification<'a>,
  specs: HashMap<Identifier, Specification<'a>>,
}

impl<'a> VerificationPlugin<'a> {
  pub fn new(target: Specification<'a>) -> Self {
    Self {
      target,
      specs: HashMap::new(),
    }
  }

  pub fn add_spec(&mut self, func_name: Identifier, spec: Specification<'a>) {
    self.specs.insert(func_name, spec);
  }
}

impl<'a> Plugin for VerificationPlugin<'a> {
  fn on_before_call<'ctx>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    func: &Function,
    _ty_args: Vec<Type>,
  ) -> PartialVMResult<bool> {
    match self.specs.get(&Identifier::new(func.name()).unwrap())  {
      Some(spec) => {
        let arg_count = func.arg_count();
        let args = plugin_ctx.operand_stack_mut().popn(arg_count.try_into().unwrap())?;
        let z3_ctx = plugin_ctx.z3_ctx();
        let solver = plugin_ctx.solver();
        solver.push();
        solver.assert(&spec.pre(z3_ctx, args.as_slice()).as_inner().not());
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
        let post_cond = spec.post(z3_ctx, args.as_slice(), returns.as_slice());
        solver.assert(post_cond.as_inner());
        // TODO: consider if at here solver is unsat
        plugin_ctx.spec_conditions_mut().push((args, post_cond));
        for val in returns {
          plugin_ctx.operand_stack_mut().push(val)?;
        }
        Ok(true)
      }
      None => Ok(false)
    }
  }

  // fn on_after_call capture the return value

  fn on_after_execute<'ctx>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    // args: &[SymValue<'ctx>],
    return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    let z3_ctx = plugin_ctx.z3_ctx();
    let ty_ctx = plugin_ctx.ty_ctx();
    let solver = plugin_ctx.solver();
    solver.push();
    solver.assert(self.target.post(z3_ctx, &[], return_values).as_inner()); // TODO: args should not be empty!!
    if solver.check() == SatResult::Sat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!("Post condition meet in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    println!("-------VERIFICATION BEGIN-------");
    println!("Counter example found! See SUGGESTION and REPORT section.");
    println!("-------VERIFICATION END---------");
    solver.pop(1);
    let path_conditions = plugin_ctx.path_conditions();
    let spec_conditions = plugin_ctx.spec_conditions();
    let pc = Bool::and(z3_ctx,
      &path_conditions.iter()
        .chain(spec_conditions.iter().map(|(_, s)| s)).map(|v| v.as_inner())
        .collect::<Vec<_>>());
    for (spec_inputs, spec) in plugin_ctx.spec_conditions().iter() {
      let spec_vars = collect_variables(spec.as_inner());
      let solver = Solver::new(z3_ctx);
      let projected = project(z3_ctx, &pc, &spec_vars).expect("Quantifier Elimination Failed!");
      let phi = spec.as_inner();
      solver.assert(phi);
      solver.assert(&projected.not());
      match solver.check() {
        SatResult::Sat => {
          let inputs = HashSet::from_iter(spec_inputs.iter().map(|v| v.as_runtime_ast(ty_ctx).unwrap()));
          let projected_input = project(z3_ctx, &pc, &inputs).expect("Quantifier Elimination Failed!");
          let suggested = Bool::and(z3_ctx, &[
            &projected_input.implies(&Bool::and(z3_ctx, &[&projected.not(), phi]).simplify()),
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
  let bounds = bounds.difference(vars).map(|v| v as &dyn Ast<'ctx>).collect::<Vec<_>>();
  goal.assert(&exists_const(ctx, &bounds, &[], cond));
  let result = tactic.apply(&goal, None)
    .list_subgoals().collect::<Vec<Goal>>();
  result.first().map(|g| Bool::and(ctx, &g.get_formulas::<Bool<'ctx>>().iter().collect::<Vec<_>>()))
}