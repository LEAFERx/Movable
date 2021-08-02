use vm::{errors::PartialVMResult, file_format::Bytecode};

use crate::{
    plugin::{Plugin, PluginContext},
};

// pub struct TODDetectionPlugin();

// impl Plugin for TODDetectionPlugin {
//     fn on_before_execute_instrcution<'ctx>(
//         &self,
//         _plugin_context: &mut dyn PluginContext<'ctx>,
//         _instruction: &Bytecode
//       ) -> PartialVMResult<()> {
//         Ok(())
//       }
    
//       fn on_before_call<'ctx>(
//         &self,
//         _plugin_context: &mut dyn PluginContext<'ctx>,
//         _func: &Function,
//         _ty_args: Vec<Type>,
//       ) -> PartialVMResult<bool> {
//         Ok(false)
//       }
    
//       fn on_before_execute<'ctx>(&self) -> VMResult<()> {
//         Ok(())
//       }
    
//       fn on_after_execute<'ctx>(
//         &self,
//         _plugin_context: &mut dyn PluginContext<'ctx>,
//         _return_values: &[SymValue<'ctx>],
//       ) -> VMResult<()> {
//         Ok(())
//       }
    
//       fn on_after_execute_user_abort<'ctx>(
//         &self,
//         _plugin_context: &mut dyn PluginContext<'ctx>,
//         _code: &SymU64<'ctx>,
//       ) -> VMResult<()> {
//         Ok(())
//       }
    
//       fn on_after_execute_abort<'ctx>(
//         &self,
//         _plugin_context: &mut dyn PluginContext<'ctx>,
//         _err: &VMError,
//       ) -> VMResult<()> {
//         Ok(())
//       }

// }