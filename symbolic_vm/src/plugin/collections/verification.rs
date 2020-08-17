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
  types::values::{SymBool, SymValue},
};

use move_vm_types::loaded_data::runtime_types::Type;

use std::{
  collections::HashMap,
  convert::TryInto,
};

use z3::SatResult;

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
  target: Specification<'a, 'ctx>,
  specs: HashMap<Identifier, Specification<'a, 'ctx>>,
}

impl<'a, 'ctx> VerificationPlugin<'a, 'ctx> {
  pub fn new(target: Specification<'a, 'ctx>) -> Self {
    Self {
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
    vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    loader: &Loader,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    func: &Function,
    ty_args: Vec<Type>,
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
        solver.assert(spec.post(args.as_slice(), returns.as_slice()).as_inner());
        for val in returns {
          interpreter.operand_stack.push(val)?;
        }
        Ok(true)
      }
      None => Ok(false)
    }
  }
}