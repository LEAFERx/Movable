use crate::{
  runtime::interpreter::SymInterpreter,
  types::values::SymIntegerValue,
};

use libra_types::{
  vm_error::{StatusCode, VMStatus},
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use z3::SatResult;

pub trait Plugin {
  fn on_before_execute_instrcution<'ctx>(
    &self,
    interpreter: &mut SymInterpreter<'_, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()>;
}

pub struct IntegerArithmeticPlugin {

}

impl IntegerArithmeticPlugin {
  pub fn new() -> Self {
    Self {}
  }
}

impl Plugin for IntegerArithmeticPlugin {
  fn on_before_execute_instrcution<'ctx>(
    &self,
    interpreter: &mut SymInterpreter<'_, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()>{
    let solver = &interpreter.solver;
    match instruction {
      Bytecode::Add => {
        solver.push();
        let lhs = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
        let rhs = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
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
            Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
          }
        }?;
        let result = bv_l.bvadd_no_overflow(bv_r, false).not();
        solver.assert(&result);
        match solver.check() {
          SatResult::Sat => {
            // let model = solver.get_model();
            println!("Add Overflow!");
          }
          _ => {}
        }
        interpreter.operand_stack.push(rhs.into_value())?;
        interpreter.operand_stack.push(lhs.into_value())?;
        solver.pop(1);
      }
      Bytecode::Sub => {
      }
      Bytecode::Mul => {

      }
      Bytecode::Div | Bytecode::Mod => {
        solver.push();

        solver.pop(1);
      }
      _ => {}
    }
    Ok(())
  }
}