use crate::{
    plugin::{collections::verification::specification::*, Plugin, PluginContext},
    runtime::{
        context::TypeContext,
        loader::{Function, Loader},
    },
    types::values::SymIntegerValue,
    types::values::SymValue,
};
use move_core_types::identifier::Identifier;
use move_vm_types::loaded_data::runtime_types::Type;
use vm::{
    errors::{PartialVMResult, VMResult},
};
use z3::{
    ast::{exists_const, forall_const, Ast, Bool, Datatype, Dynamic},
    Context, Goal, SatResult, Solver, Tactic,
};
pub struct TDDetectionPlugin {
    now_microseconds_used: bool,
    timestamp_symbol: Option<u64>,
}

impl TDDetectionPlugin {
    pub fn new() -> Self {
        Self {
            now_microseconds_used: false,
            timestamp_symbol: None,
        }
    }
}

impl Plugin for TDDetectionPlugin {
    fn on_before_call<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        func: &Function,
        _ty_args: Vec<Type>,
    ) -> PartialVMResult<bool> {
        if func.name() == "now_microseconds" {
            self.now_microseconds_used = true;
            let ty_ctx = plugin_ctx.ty_ctx();
            let z3_ctx = plugin_ctx.z3_ctx();
            self.timestamp_symbol = Some(rand::random::<u64>());
            let model = plugin_ctx.solver();
            let mem_key_sort = ty_ctx.memory_key_sort();
            let timestamp_val = Datatype::fresh_const(z3_ctx, "timestamp", &mem_key_sort.sort);
            plugin_ctx
                .memory_mut()
                .write_resource(z3_ctx, ty_ctx, timestamp_val);
            Ok(true)
        }
        Ok(false)
    }

    fn on_after_execute<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        return_values: &[SymValue<'ctx>],
    ) -> VMResult<()> {
        if self.now_microseconds_used {
            if let Some(timestamp_symbol) = self.timestamp_symbol {
                let solver = plugin_ctx.solver();
                let model = solver.get_model().unwrap();
                let ty_ctx = plugin_ctx.ty_ctx();
                let z3_ctx = plugin_ctx.z3_ctx();
                let timestamp_val =
                    plugin_ctx
                        .memory_mut()
                        .load_resource(z3_ctx, ty_ctx, &model, "timestamp").unwrap();
                let bv_r = SymIntegerValue::U64();
                let manipulation_cond = timestamp_val.gt(bv_r);
                solver.assert(&manipulation_cond.not());

                match solver.check() {
                    SatResult::Sat => {
                        println!("Block Timestamp Manipulation detected!");
                    }
                    _ => {}
                }
            }
        }
        Ok(())
    }
}
