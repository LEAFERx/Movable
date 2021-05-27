use crate::{
  plugin::{Plugin, PluginContext},
  types::values::SymIntegerValue,
};

use move_core_types::vm_status::StatusCode;

use vm::{
  errors::*,
  file_format::Bytecode,
};

use z3::SatResult;

pub struct IntegerArithmeticPlugin();

impl IntegerArithmeticPlugin {
  pub fn new() -> Self {
    Self {}
  }
}

impl<'ctx> Plugin<'ctx> for IntegerArithmeticPlugin {
  fn on_before_execute_instrcution<'vtxn>(
    &self,
    plugin_ctx: &mut dyn PluginContext<'ctx>,
    instruction: &Bytecode
  ) -> PartialVMResult<()>{
    match instruction {
      Bytecode::Add => {
        plugin_ctx.solver().push();
        let lhs = plugin_ctx.operand_stack_mut().pop_as::<SymIntegerValue>()?;
        let rhs = plugin_ctx.operand_stack_mut().pop_as::<SymIntegerValue>()?;
        let (bv_l, bv_r) = match (&lhs, &rhs) {
          (SymIntegerValue::U8(l), SymIntegerValue::U8(r)) => {
            Ok((l.as_inner(), r.as_inner()))
          }
          (SymIntegerValue::U64(l), SymIntegerValue::U64(r)) => {
            Ok((l.as_inner(), r.as_inner()))
          }
          (SymIntegerValue::U128(l), SymIntegerValue::U128(r)) => {
            Ok((l.as_inner(), r.as_inner()))
          }
          (l, r) => {
            let msg = format!("Cannot add {:?} and {:?}", l, r);
            Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
          }
        }?;
        let result = bv_l.bvadd_no_overflow(bv_r, false).not();
        plugin_ctx.solver().assert(&result);
        match plugin_ctx.solver().check() {
          SatResult::Sat => {
            // let model = solver.get_model();
            println!("Add Overflow!");
          }
          _ => {}
        }
        plugin_ctx.operand_stack_mut().push(rhs.into_value())?;
        plugin_ctx.operand_stack_mut().push(lhs.into_value())?;
        plugin_ctx.solver().pop(1);
      }
      Bytecode::Sub => {
      }
      Bytecode::Mul => {

      }
      Bytecode::Div | Bytecode::Mod => {
        plugin_ctx.solver().push();

        plugin_ctx.solver().pop(1);
      }
      _ => {}
    }
    Ok(())
  }
}