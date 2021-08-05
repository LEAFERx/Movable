use move_vm_types::loaded_data::runtime_types::Type;
use vm::{errors::{PartialVMResult, VMResult}, file_format::Bytecode};
use crate::{
  plugin::{Plugin, PluginContext, collections::verification::specification::*},
  runtime::{
    context::TypeContext,
    loader::{Loader, Function}}, types::values::{SymValue}, types::values::SymIntegerValue,
};
use move_core_types::identifier::Identifier;
use crate::types::memory::SymMemory;
use vm::errors::VMError;
use crate::types::values::SymU64;

pub struct TODDetectionPlugin();

impl TODDetectionPlugin {
    pub fn new() -> Self {
        Self {}
    }
}

impl Plugin for TODDetectionPlugin {
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
    
      fn on_after_execute_user_abort<'ctx>(
        &self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        _code: &SymU64<'ctx>,
      ) -> VMResult<()> {
        Ok(())
      }
    
      fn on_after_execute_abort<'ctx>(
        &self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        _err: &VMError,
      ) -> VMResult<()> {
        Ok(())
      }

}