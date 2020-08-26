use vm::{
  errors::*,
};
use libra_types::{
  account_address::AccountAddress,
  vm_error::{StatusCode, VMStatus},
};
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
pub struct SymAccountAddress<'ctx>(BV<'ctx>);

impl<'ctx> SymAccountAddress<'ctx> {
  pub const LENGTH: usize = AccountAddress::LENGTH;

  pub fn new(context: &'ctx Context, address: AccountAddress) -> Self {
    let value = u128::from_ne_bytes(address.into());
    let bv = BV::from_u64(context, (value >> 64) as u64, 64)
      .concat(&BV::from_u64(context, value as u64, 64));
    Self(bv)
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    Self(ast)
  }

  pub fn into_address(self) -> VMResult<AccountAddress> {
    let high = self.0.extract(127, 64).simplify();
    let low = self.0.extract(63, 0).simplify();
    
    match (high.as_u64(), low.as_u64()) {
      (Some(high), Some(low)) => {
        let bytes = [high.to_ne_bytes(), low.to_ne_bytes()].concat();
        // simply unwrap here since we know bytes is always [u8; 16]
        Ok(bytes.try_into().unwrap())
      },
      _ => Err(
        VMStatus::new(StatusCode::INVALID_DATA)
          .with_message(format!("Cannot make symbolic address {:?} to concrete.", self))
      ),
    }
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    Ok(SymBool::from_ast(self.0._eq(&other.0)))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymAccountAddress<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.0))
  }
}
