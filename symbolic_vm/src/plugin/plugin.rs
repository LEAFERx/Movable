use crate::{
  runtime::{
    interpreter::SymInterpreter,
    loader::{Loader, Function},
  },
  state::{
    vm_context::SymbolicVMContext,
  },
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use move_vm_types::loaded_data::runtime_types::Type;

pub trait Plugin<'ctx> {
  fn on_before_execute_instrcution<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()> {
    Ok(())
  }

  fn on_before_call<'vtxn>(
    &self,
    vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    loader: &Loader,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    func: &Function,
    ty_args: Vec<Type>,
  ) -> VMResult<bool> {
    Ok(false)
  }
}
