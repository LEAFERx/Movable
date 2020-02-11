use vm::{
  errors::*,
};
use libra_types::{
  account_address::AccountAddress,
  vm_error::{StatusCode, VMStatus},
};
use z3::{
  ast, Context
};

#[derive(Debug, Clone)]
pub struct SymAccountAddress<'ctx> {
  ctx: &'ctx Context,
  address: AccountAddress,
}

impl<'ctx> SymAccountAddress<'ctx> {
  pub fn new(ctx: &'ctx Context, address: AccountAddress) -> Self {
    SymAccountAddress {
      ctx,
      address,
    }
  }

  pub fn equals(&self, other: &Self) -> VMResult<ast::Bool<'ctx>> {
    if self.ctx != other.ctx {
      let msg = format!("Equals on struct with different context: {:?} and {:?}", self, other);
      return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
    }
    Ok(ast::Bool::from_bool(self.ctx, self.address == other.address))
  }
}
