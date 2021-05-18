use crate::{
  runtime::{
    interpreter::SymInterpreter,
    loader::{Loader, Function},
  },
  state::{
    vm_context::SymbolicVMContext,
  },
  types::values::SymValue,
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use move_vm_types::loaded_data::runtime_types::Type;

pub trait Plugin<'ctx> {
  fn on_before_execute_instrcution<'vtxn>(
    &self,
    _interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    _instruction: &Bytecode
  ) -> PartialVMResult<()> {
    Ok(())
  }

  fn on_before_call<'vtxn>(
    &self,
    _vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    _loader: &Loader,
    _interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    _func: &Function,
    _ty_args: Vec<Type>,
  ) -> PartialVMResult<bool> {
    Ok(false)
  }

  fn on_before_execute<'vtxn>(&self) -> PartialVMResult<()> {
    Ok(())
  }

  fn on_after_execute<'vtxn>(
    &self,
    _interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    _return_values: &[SymValue<'ctx>],
  ) -> PartialVMResult<()> {
    Ok(())
  }
}
