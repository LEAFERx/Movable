use move_core_types::{
  identifier::Identifier,
  language_storage::TypeTag,
};

use vm::{
  errors::*,
  file_format::SignatureToken,
};

use crate::{
  plugin::{Plugin, PluginContext, collections::verification::specification::*},
  runtime::{
    context::TypeContext,
    loader::{Loader, Function},
  },
  types::{
    memory::SymMemory,
    values::{SymBool, SymValue, SymbolicMoveValue, SymU64, SymAccountAddress},
  },
};

use move_vm_types::loaded_data::runtime_types::Type;

use std::{
  collections::{HashMap, HashSet, VecDeque},
  convert::TryInto,
  iter::FromIterator,
};

use z3::{
  ast::{Ast, Bool, Datatype, Dynamic, exists_const, forall_const},
  Context,
  Goal,
  Solver,
  SatResult,
  Tactic,
};
use z3_sys::AstKind;

pub struct VerificationPlugin<'a> {
  target: FunctionSpec<'a>,
  specs: HashMap<Identifier, FunctionSpec<'a>>,
}

impl<'a> VerificationPlugin<'a> {
  pub fn new(target: FunctionSpec<'a>) -> Self {
    Self {
      target,
      specs: HashMap::new(),
    }
  }

  pub fn add_spec(&mut self, func_name: Identifier, spec: FunctionSpec<'a>) {
    self.specs.insert(func_name, spec);
  }
}

impl<'a> Plugin for VerificationPlugin<'a> {
  fn on_before_call<'ctx>(
    &mut self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    func: &Function,
    _ty_args: Vec<Type>,
  ) -> PartialVMResult<bool> {
    match self.specs.get(&Identifier::new(func.name()).unwrap())  {
      Some(spec) => {
        println!("Opaque call for function {:?}", func.name());
        let arg_count = func.arg_count();
        let args = plugin_ctx.operand_stack_mut().popn(arg_count.try_into().unwrap())?;
        let z3_ctx = plugin_ctx.z3_ctx();
        let ty_ctx = plugin_ctx.ty_ctx();
        let memory = plugin_ctx.memory();
        let solver = plugin_ctx.solver();
        solver.push();
        solver.assert(&spec.requires(z3_ctx, ty_ctx, args.as_slice(), memory).as_inner().not());
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
        let new_memory = SymMemory::new(z3_ctx, ty_ctx);
        let no_abort = spec.aborts_if(z3_ctx, ty_ctx, args.as_slice(), memory).as_inner().not();
        let post_cond = spec.ensures(z3_ctx, ty_ctx, args.as_slice(), returns.as_slice(), memory, &new_memory);
        let modifies = spec.modifies(z3_ctx, ty_ctx, args.as_slice(), memory);
        let modifies_cond = modifies_condition(
          z3_ctx,
          ty_ctx,
          modifies,
          memory,
          &new_memory,
        );
        let opaque_cond = Bool::and(z3_ctx, &[&no_abort, post_cond.as_inner(), &modifies_cond]);
        solver.assert(&opaque_cond);
        println!("{:?}", solver);
        // TODO: consider if at here solver is unsat
        if SatResult::Unsat == solver.check() {
          println!("{:?}", solver);
          panic!("After asserting the opaque post condition, the path condition becomes Unsat!");
        }
        println!("Opaque cond asserted");
        plugin_ctx.spec_conditions_mut().push((args, SymBool::from_ast(opaque_cond)));
        for val in returns {
          plugin_ctx.operand_stack_mut().push(val)?;
        }
        *plugin_ctx.memory_mut() = new_memory;
        Ok(true)
      }
      None => Ok(false)
    }
  }

  // fn on_after_call capture the return value

  fn on_after_execute<'ctx>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    let z3_ctx = plugin_ctx.z3_ctx();
    let ty_ctx = plugin_ctx.ty_ctx();
    let args = plugin_ctx.args();
    let old_memory = plugin_ctx.old_memory();
    let memory = plugin_ctx.memory();
    let solver = plugin_ctx.solver();

    solver.push();
    solver.assert(self.target.aborts_if(z3_ctx, ty_ctx, args, old_memory).as_inner());
    if solver.check() == SatResult::Sat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!(">>> FAILURE");
      println!("Aborts if condition may meet in this path! This path should NOT abort!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    solver.pop(1);

    solver.push();
    let modifies_cond = modifies_condition(
      z3_ctx,
      ty_ctx,
      self.target.modifies(z3_ctx, ty_ctx, args, old_memory),
      old_memory,
      memory,
    );
    solver.assert(&modifies_cond.not());
    if solver.check() == SatResult::Sat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!(">>> FAILURE");
      println!("Modifies may not meet in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    solver.pop(1);

    solver.push();
    solver.assert(&self.target.ensures(z3_ctx, ty_ctx, args, return_values, old_memory, memory).as_inner().not());
    if solver.check() == SatResult::Unsat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!(">>> SUCCESS");
      println!("Post condition always met in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    println!("-------VERIFICATION BEGIN-------");
    println!(">>> FAILURE");
    println!("Post condition voilated! Counter example found! See SUGGESTION and REPORT section.");
    println!("-------VERIFICATION END---------");
    solver.pop(1);
    let path_conditions = plugin_ctx.path_conditions();
    let spec_conditions = plugin_ctx.spec_conditions();
    let pc = Bool::and(z3_ctx,
      &path_conditions.iter()
        .chain(spec_conditions.iter().map(|(_, s)| s))
        .map(|v| v.as_inner())
        .collect::<Vec<_>>(),
    );
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
            &projected_input.not().implies(phi)],
          );
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

  fn on_after_execute_abort<'ctx>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    _err: &VMError,
  ) -> VMResult<()> {
    let z3_ctx = plugin_ctx.z3_ctx();
    let ty_ctx = plugin_ctx.ty_ctx();
    let args = plugin_ctx.args();
    let old_memory = plugin_ctx.old_memory();
    let solver = plugin_ctx.solver();

    solver.push();
    solver.assert(&self.target.aborts_if(z3_ctx, ty_ctx, args, old_memory).as_inner().not());
    if solver.check() == SatResult::Unsat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!(">>> SUCCESS");
      println!("Aborts if condition always met in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    println!("-------VERIFICATION BEGIN-------");
    println!(">>> FAILURE");
    println!("Aborts if condition violated! Counter example found!");
    println!("-------VERIFICATION END---------");
    solver.pop(1);
    Ok(())
  }

  fn on_after_execute_user_abort<'ctx>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    _code: &SymU64<'ctx>,
  ) -> VMResult<()> {
    let z3_ctx = plugin_ctx.z3_ctx();
    let ty_ctx = plugin_ctx.ty_ctx();
    let args = plugin_ctx.args();
    let old_memory = plugin_ctx.old_memory();
    let solver = plugin_ctx.solver();

    solver.push();
    solver.assert(&self.target.aborts_if(z3_ctx, ty_ctx, args, old_memory).as_inner().not());
    if solver.check() == SatResult::Unsat {
      solver.pop(1);
      println!("-------VERIFICATION BEGIN-------");
      println!(">>> SUCCESS");
      println!("Aborts if always condition met in this path!");
      println!("-------VERIFICATION END---------");
      return Ok(());
    }
    println!("-------VERIFICATION BEGIN-------");
    println!(">>> FAILURE");
    println!("Aborts if condition violated! Counter example found!");
    println!("-------VERIFICATION END---------");
    solver.pop(1);
    Ok(())
  }
}

fn collect_variables<'ctx>(var: &impl Ast<'ctx>) -> HashSet<Dynamic<'ctx>> {
  let mut queue: VecDeque<Dynamic<'ctx>> = VecDeque::new();
  let mut result = HashSet::new();
  queue.push_back(Dynamic::from_ast(var));
  loop {
    match queue.pop_front() {
      Some(v) => {
        if AstKind::App == v.kind() {
          if v.children().len() == 0 {
            // Discard constant boolean
            if let Some(b) = v.as_bool() {
              if let Some(_) = b.as_bool() {
                continue;
              }
            }
            // Discard constant string
            if let Some(s) = v.as_string() {
              if let Some(_) = s.as_string() {
                continue;
              }
            }
            result.insert(v);
          } else {
            queue.append(&mut VecDeque::from(v.children()));
          }
        }
      },
      None => break,
    }
  }
  return result;
}

fn project<'ctx>(z3_ctx: &'ctx Context, cond: &Bool<'ctx>, vars: &HashSet<Dynamic<'ctx>>) -> Option<Bool<'ctx>> {
  let tactic = Tactic::new(z3_ctx, "qe"); //.and_then(&Tactic::new(ctx, "simplify"));
  let goal = Goal::new(z3_ctx, false, false, false);
  let bounds = collect_variables(cond);
  let bounds = bounds.difference(vars).map(|v| v as &dyn Ast<'ctx>).collect::<Vec<_>>();
  goal.assert(&exists_const(z3_ctx, &bounds, &[], cond));
  let result = tactic.apply(&goal, None)
    .list_subgoals().collect::<Vec<Goal>>();
  result.first().map(|g| Bool::and(z3_ctx, &g.get_formulas::<Bool<'ctx>>().iter().collect::<Vec<_>>()))
}

fn modifies_condition<'ctx>(
  z3_ctx: &'ctx Context,
  ty_ctx: &TypeContext<'ctx>,
  modifies: Vec<(SymAccountAddress<'ctx>, TypeTag)>,
  old_memory: &SymMemory<'ctx>,
  memory: &SymMemory<'ctx>,
) -> Bool<'ctx> {
  let mem_key_sort = ty_ctx.memory_key_sort();
  let key = Datatype::fresh_const(z3_ctx, "ModifiesConditionKey", &mem_key_sort.sort);
  let not_equal_modified_keys: Vec<_> = modifies.into_iter().map(
    |(addr, ty)| ty_ctx.make_memory_key(addr, ty)._eq(&key).not()
  ).collect();
  let not_equal_modified_keys_ref: Vec<_> = not_equal_modified_keys.iter().collect();
  let key_not_equal = Bool::and(z3_ctx, &not_equal_modified_keys_ref);
  let old_memory_val = old_memory.get_raw(&key);
  let memory_val = memory.get_raw(&key);
  let memory_equal = old_memory_val._eq(&memory_val);
  let modifies_cond = key_not_equal.implies(&memory_equal);
  forall_const(
    z3_ctx,
    &[&key],
    &[],
    &modifies_cond,
  )
}
