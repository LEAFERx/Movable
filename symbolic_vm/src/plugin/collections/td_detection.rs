use crate::{
    plugin::{collections::verification::specification::*, Plugin, PluginContext},
    runtime::{
        context::TypeContext,
        loader::{Function, Loader},
    },
    types::values::{SymIntegerValue, SymU64, SymValue},
};
use move_core_types::{identifier::Identifier, language_storage::TypeTag};
use move_vm_types::loaded_data::runtime_types::Type;
use vm::errors::{PartialVMResult, VMError, VMResult};
use z3::{
    ast::{exists_const, forall_const, Ast, Bool, Datatype, Dynamic, BV},
    Context, Goal, SatResult, Solver, Tactic,
};
pub struct TDDetectionPlugin {
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
        let solver = plugin_ctx.solver();
        let z3_ctx = plugin_ctx.z3_ctx();
        if self.now_microseconds_used {
            let path_conditions = plugin_ctx.path_conditions();

            // if let Some(timestamp_symbol) = self.timestamp_symbol {
            let timestamp_symbol = z3::ast::BV::new_const(plugin_ctx.z3_ctx(), "timestamp", 64); // pretend the path condition has the variable names the same timestamp
            let manipulation_cond = timestamp_symbol.bvsgt(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));
            let manipulation_cond1 = Bool::and(
                z3_ctx,
                &path_conditions
                    .iter()
                    .map(|v| v.as_inner())
                    .chain(vec![manipulation_cond].iter())
                    .collect::<Vec<_>>(),
            );
            solver.push();
            solver.assert(&manipulation_cond1);
            // fmt::format(&solver);
            match solver.check() {
                SatResult::Unsat => {
                    let manipulation_cond2 =
                        timestamp_symbol.bvsle(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));
                    let manipulation_cond3 = Bool::and(
                        z3_ctx,
                        &path_conditions
                            .iter()
                            .map(|v| v.as_inner())
                            .chain(vec![manipulation_cond2].iter())
                            .collect::<Vec<_>>(),
                    );
                    solver.assert(&manipulation_cond3);
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
        solver.pop(1);
        Ok(())
    }
    fn on_after_execute_abort<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        _err: &VMError,
    ) -> VMResult<()> {
        Ok(())
    }
    fn on_after_execute_user_abort<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        _code: &SymU64<'ctx>,
    ) -> VMResult<()> {
        Ok(())
    }
}
