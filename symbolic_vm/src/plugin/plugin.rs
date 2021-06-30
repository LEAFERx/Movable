use crate::{
  runtime::{
    context::TypeContext,
    interpreter::{SymStack, SymCallStack},
    loader::{Loader, Function},
  },
  types::values::{SymValue, SymBool},
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use move_vm_types::loaded_data::runtime_types::Type;

use z3::{Context, Solver};

pub trait PluginContext<'ctx> {
  fn z3_ctx(&self) -> &'ctx Context;
  fn ty_ctx(&self) -> &TypeContext<'ctx>;
  fn solver(&self) -> &Solver<'ctx>;

  fn operand_stack(&self) -> &SymStack<'ctx>;
  fn path_conditions(&self) -> &Vec<SymBool<'ctx>>;
  fn spec_conditions(&self) -> &Vec<(Vec<SymValue<'ctx>>, SymBool<'ctx>)>;
  
  fn operand_stack_mut(&mut self) -> &mut SymStack<'ctx>;
  fn path_conditions_mut(&mut self) -> &mut Vec<SymBool<'ctx>>;
  fn spec_conditions_mut(&mut self) -> &mut Vec<(Vec<SymValue<'ctx>>, SymBool<'ctx>)>;
}

pub trait Plugin {
  fn on_before_execute_instrcution<'ctx>(
    &self,
    _plugin_context: &mut dyn PluginContext<'ctx>,
    _instruction: &Bytecode
  ) -> PartialVMResult<()> {
    Ok(())
  }

  fn on_before_call<'ctx>(
    &self,
    _plugin_context: &mut dyn PluginContext<'ctx>,
    _func: &Function,
    _ty_args: Vec<Type>,
  ) -> PartialVMResult<bool> {
    Ok(false)
  }

  fn on_before_execute<'ctx>(&self) -> VMResult<()> {
    Ok(())
  }

  fn on_after_execute<'ctx>(
    &self,
    _plugin_context: &mut dyn PluginContext<'ctx>,
    _return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    Ok(())
  }
}
