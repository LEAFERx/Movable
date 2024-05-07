use crate::{
    plugin::{collections::verification::specification::*, Plugin, PluginContext},
    runtime::{
        context::TypeContext,
        loader::{Function, Loader},
    },
    types::values::SymIntegerValue,
    types::values::SymValue,
};
use move_core_types::{identifier::Identifier, language_storage::TypeTag};
use move_vm_types::loaded_data::runtime_types::Type;
use vm::errors::{PartialVMResult, VMResult};
use z3::{
    ast::{exists_const, forall_const, Ast, Bool, Datatype, Dynamic, BV},
    Context, Goal, SatResult, Solver, Tactic,
};
pub struct TDDetectionPlugin  {
    now_microseconds_used: bool,
}

impl TDDetectionPlugin {
    pub fn new() -> Self {
        Self {
            now_microseconds_used: false,
        }
    }
}

impl Plugin for TDDetectionPlugin {
    fn on_before_call<'ctx>(
        &mut self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        func: &Function,
        _ty_args: Vec<Type>,
    ) -> PartialVMResult<bool> {
        if func.name() == "now_microseconds" {
            self.now_microseconds_used = true;
            let ty_ctx = plugin_ctx.ty_ctx();
            let z3_ctx = plugin_ctx.z3_ctx();
            // self.timestamp_symbol = Some(&z3::ast::BV::new_const(&z3_ctx, "timestamp", 64));
            return Ok(true);
        }
        Ok(false)
    }

    fn on_after_execute<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        return_values: &[SymValue<'ctx>],
    ) -> VMResult<()> {
        if self.now_microseconds_used {
            // if let Some(timestamp_symbol) = self.timestamp_symbol {
                let timestamp_symbol = z3::ast::BV::new_const(plugin_ctx.z3_ctx(), "timestamp", 64);// pretend the path condition has the variable names the same timestamp
                let solver = plugin_ctx.solver();
                let model = solver.get_model().unwrap();
                let ty_ctx = plugin_ctx.ty_ctx();
                let z3_ctx = plugin_ctx.z3_ctx();
                let manipulation_cond =
                    timestamp_symbol.bvsgt(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));

                solver.assert(&manipulation_cond);
                // fmt::format(&solver);
                match solver.check() {
                    SatResult::Unsat => {
                        let manipulation_cond1 =
                            timestamp_symbol.bvsle(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));

                        solver.assert(&manipulation_cond1);
                        match solver.check() {
                            SatResult::Sat => {
                                println!("Block Timestamp Manipulation detected!");
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
            // }
        }
        Ok(())
    }
}
