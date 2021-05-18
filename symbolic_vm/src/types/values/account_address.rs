use vm::{
  errors::*,
};
use diem_types::account_address::AccountAddress;
use move_core_types::vm_status::StatusCode;
use std::convert::TryInto;
use z3::{
  ast::{Ast, BV, Dynamic},
  Context,
};
use crate::types::values::{
  primitives::SymBool,
  SymbolicMoveValue,
};

#[derive(Debug, Clone)]
pub struct SymAccountAddress<'ctx> {
  ast: BV<'ctx>,
}

impl<'ctx> SymAccountAddress<'ctx> {
  pub const LENGTH: usize = AccountAddress::LENGTH;

  pub fn new(z3_ctx: &'ctx Context, address: AccountAddress) -> Self {
    let value = u128::from_ne_bytes(address.into());
    let ast = BV::from_u64(z3_ctx, (value >> 64) as u64, 64)
      .concat(&BV::from_u64(z3_ctx, value as u64, 64));
    Self {
      ast,
    }
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    Self { ast }
  }

  pub fn into_address(self) -> PartialVMResult<AccountAddress> {
    let high = self.ast.extract(127, 64).simplify();
    let low = self.ast.extract(63, 0).simplify();
    
    match (high.as_u64(), low.as_u64()) {
      (Some(high), Some(low)) => {
        let bytes = [high.to_ne_bytes(), low.to_ne_bytes()].concat();
        // simply unwrap here since we know bytes is always [u8; 16]
        Ok(bytes.try_into().unwrap())
      },
      _ => Err(
        PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
          .with_message(format!("Cannot make symbolic address {:?} to concrete.", self))
      ),
    }
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool::from_ast(self.ast._eq(&other.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymAccountAddress<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}
