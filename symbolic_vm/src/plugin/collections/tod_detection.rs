use std::path;

use crate::types::memory::SymMemory;
use crate::types::values::SymU64;
use crate::{
    plugin::{collections::verification::specification::*, Plugin, PluginContext},
    runtime::{
        context::TypeContext,
        loader::{Function, Loader},
    },
    types::values::SymIntegerValue,
    types::values::{SymBool, SymValue},
};
use move_core_types::identifier::Identifier;
use move_vm_types::loaded_data::runtime_types::Type;
use vm::errors::VMError;
use vm::{
    errors::{PartialVMResult, VMResult},
    file_format::Bytecode,
};
use z3::{ast::Bool, SatResult};

pub struct TODDetectionPlugin<'a> {
    tod_transaction1: bool,
    tod_transaction2: bool,
    path_conditions1: Vec<SymBool<'a>>,
    path_conditions2: Vec<SymBool<'a>>,
}

impl TODDetectionPlugin<'_> {
    pub fn new() -> Self {
        Self {
            tod_transaction1: false,
            tod_transaction2: false,
            path_conditions1: vec![],
            path_conditions2: vec![],
        }
    }
}

impl Plugin for TODDetectionPlugin<'_> {
    fn on_before_execute_instrcution<'ctx>(
        &self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        _instruction: &Bytecode,
    ) -> PartialVMResult<()> {
        Ok(())
    }

    fn on_before_call<'ctx>(
        &mut self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        func: &Function,
        _ty_args: Vec<Type>,
    ) -> PartialVMResult<bool> {
        if func.name().contains("TOD_Transaction") {
            self.tod_transaction1 = true;
            self.path_conditions1 = plugin_ctx.path_conditions_mut().iter().cloned().collect();
            return Ok(true);
        }
        if self.tod_transaction1 && func.name().contains("TOD_Transaction") {
            self.tod_transaction2 = true;
            self.path_conditions2 = plugin_ctx.path_conditions_mut().iter().cloned().collect();
            return Ok(true);
        }
        Ok(false)
    }

    fn on_after_execute<'ctx>(
        &self,
        plugin_ctx: &mut dyn PluginContext<'ctx>,
        return_values: &[SymValue<'ctx>],
    ) -> VMResult<()> {
        if self.tod_transaction1 && self.tod_transaction2 {
            let solver = plugin_ctx.solver();
            let solver_copy = solver.clone();
            let model = solver.get_model().unwrap();
            let ty_ctx = plugin_ctx.ty_ctx();
            let z3_ctx = plugin_ctx.z3_ctx();
            solver.assert(&Bool::and(
                z3_ctx,
                &self
                    .path_conditions1
                    .iter()
                    .map(|v| v.as_inner())
                    .collect::<Vec<_>>(),
            ));
            solver_copy.assert(&Bool::and(
                z3_ctx,
                &self
                    .path_conditions1
                    .iter()
                    .chain(self.path_conditions2.iter().map(|s| s))
                    .map(|v| v.as_inner())
                    .collect::<Vec<_>>(),
            ));
            // fmt::format(&solver);
            match solver.check() {
                SatResult::Sat => match solver_copy.check() {
                    SatResult::Unsat => {}
                    _ => {
                        println!("Transactional Dependency Manipulation detected!");
                    }
                },
                _ => {
                    println!("Transactional Dependency Manipulation detected!");
                }
            }
        }
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
