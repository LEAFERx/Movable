use move_vm_types::loaded_data::runtime_types::Type;
use vm::{errors::{PartialVMResult, VMResult}, file_format::Bytecode, normalized::Function};

use crate::{plugin::{Plugin, PluginContext}, types::values::{SymValue}, types::values::SymIntegerValue};

pub struct TDDetectionPlugin();

impl Plugin for TDDetectionPlugin {
      fn on_after_execute<'ctx>(
        &self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        _return_values: &[SymValue<'ctx>],
      ) -> VMResult<()> {
        
        Ok(())
      }

}