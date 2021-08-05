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

pub struct TDDetectionPlugin();

impl TDDetectionPlugin {
    pub fn new() -> Self {
        Self {}
    }
}

impl Plugin for TDDetectionPlugin {
    /** Get the initial change set and insert into SymMemory one by one */
    fn on_before_call<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        func: &Function,
        _ty_args: Vec<Type>,
    ) -> PartialVMResult<bool> {
        println!("[TD]: Change Set into SymMemory {:?}", func.name());
        let args = plugin_ctx.data_store();
        let z3_ctx = plugin_ctx.z3_ctx();
        let ty_ctx = plugin_ctx.ty_ctx();

        let memory = plugin_ctx.memory_mut();
        let solver = plugin_ctx.solver();
        Ok(true)
    }
    fn on_after_execute<'ctx>(
        &self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        _return_values: &[SymValue<'ctx>],
    ) -> VMResult<()> {
        Ok(())
    }
}