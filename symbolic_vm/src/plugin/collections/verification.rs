use move_core_types::{
  identifier::Identifier,
};

use libra_types::{
  vm_error::{StatusCode, VMStatus},
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
  collections::HashMap,
  convert::TryInto,
};

use z3::{ast::{Bool, Dynamic}, Context, Solver, SatResult};

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
  context: &'ctx Context,
  target: Specification<'a, 'ctx>,
  specs: HashMap<Identifier, Specification<'a, 'ctx>>,
}

impl<'a, 'ctx> VerificationPlugin<'a, 'ctx> {
  pub fn new(context: &'ctx Context, target: Specification<'a, 'ctx>) -> Self {
    Self {
      context,
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
  ) -> VMResult<bool> {
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
        // !!! should consider generics, substitude ty_args
        // !!! also model other type of returns
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
        // !!! consider if at here solver is unsat
        interpreter.spec_conditions.push((args, post_cond));
        for val in returns {
          interpreter.operand_stack.push(val)?;
        }
        Ok(true)
      }
      None => Ok(false)
    }
  }

  fn on_after_execute<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    interpreter.solver.push();
    interpreter.solver.assert(self.target.post(&[], return_values).as_inner()); // !!! args should not be empty!!
    if interpreter.solver.check() == SatResult::Sat {
      interpreter.solver.pop(1);
      return Ok(());
    }
    interpreter.solver.pop(1);
    for (spec_inputs, spec) in interpreter.spec_conditions.iter() {
      let spec_vars = spec.operand();
      let solver = Solver::new(self.context);
      let mut projected = vec![];
      // Projections
      for cond in interpreter.path_conditions.iter().chain(interpreter.spec_conditions.iter().map(|(_, s)| s)) {
        // do not need to check self
        if cond.as_inner() == spec.as_inner() {
          projected.push(cond);
          continue;
        }
        let mut flag = true;
        for var in cond.operand().iter() {
          let mut flag1 = false;
          for spec_var in spec_vars.iter() {
            if var == spec_var {
              flag1 = true;
              break;
            }
          }
          if !flag1 {
            flag = false;
            break;
          }
        }
        if flag {
          projected.push(cond);
        }
      }
      let phi = spec.as_inner();
      let b = Bool::and(self.context, &projected.iter().map(|b| b.as_inner()).collect::<Vec<_>>());
      let b_not = b.not();
      solver.assert(phi);
      solver.assert(&b_not);
      match solver.check() {
        SatResult::Sat => {
          let mut projected_input = vec![];
          // Project inputs
          for cond in interpreter.path_conditions.iter().chain(interpreter.spec_conditions.iter().map(|(_, s)| s)) {
            // do not need to check self
            let mut flag = true;
            for var in cond.operand().iter() {
              let mut flag1 = false;
              for spec_var in spec_inputs.iter() {
                if var == &spec_var.as_ast()? {
                  flag1 = true;
                  break;
                }
              }
              if !flag1 {
                flag = false;
                break;
              }
            }
            if flag {
              projected_input.push(cond);
            }
          }
          let i = Bool::and(self.context, &projected_input.iter().map(|b| b.as_inner()).collect::<Vec<_>>());
          println!("-------SUGGESTION BEGIN-------");
          println!("previous condition:");
          println!("{:#?}", spec.as_inner());
          println!("suggested condition:");
          println!("{:#?}", i.implies(&b));
          println!("-------SUGGESTION END---------");
        },
        _ => {}
      }
    }
    Ok(())
  }
}
