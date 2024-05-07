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

pub struct TODDetectionPlugin {
  tod_transaction1: bool,
  tod_transaction2: bool,
  
}

impl TODDetectionPlugin {
    pub fn new() -> Self {
        Self {
            tod_transaction1: false,
            tod_transaction2: false
        }
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
        &mut self,
        _plugin_context: &mut dyn PluginContext<'ctx>,
        func: &Function,
        _ty_args: Vec<Type>,
      ) -> PartialVMResult<bool> {
        if func.name().contains("TOD_Transaction") {
          self.tod_transaction1 = true;
          return Ok(true);
        }
        if self.tod_transaction1 && func.name().contains("TOD_Transaction") {
          self.tod_transaction2 = true;
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
          let owner_symbol = z3::ast::BV::new_const(plugin_ctx.z3_ctx(), "owner", 64);
          let solver = plugin_ctx.solver();
          let model = solver.get_model().unwrap();
          let ty_ctx = plugin_ctx.ty_ctx();
          let z3_ctx = plugin_ctx.z3_ctx();
          let manipulation_cond =
              owner_symbol.bvsgt(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));

          solver.assert(&manipulation_cond);
          // fmt::format(&solver);
          match solver.check() {
              SatResult::Unsat => {
                  let manipulation_cond1 =
                      owner_symbol.bvsle(&z3::ast::BV::from_i64(&z3_ctx, 1, 64));

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