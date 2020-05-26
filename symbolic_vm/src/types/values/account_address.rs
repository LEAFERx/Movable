use vm::{
  errors::*,
};
use libra_types::{
  account_address::AccountAddress,
  vm_error::{StatusCode, VMStatus},
};

use solver::Solver;
use crate::types::values::{
  primitives::SymBool,
};

#[derive(Debug, Clone)]
pub struct SymAccountAddress<'ctx> {
  solver: &'ctx Solver<'ctx>,
  address: AccountAddress,
}

impl<'ctx> SymAccountAddress<'ctx> {
  pub const LENGTH: usize = AccountAddress::LENGTH;

  pub fn new(solver: &'ctx Solver<'ctx>, address: AccountAddress) -> Self {
    SymAccountAddress {
      solver,
      address,
    }
  }

  pub fn into_address(self) -> AccountAddress {
    self.address
  }

  pub fn short_str(&self) -> String {
    self.address.short_str()
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    if self.solver != other.solver {
      let msg = format!("Equals on struct with different solver context: {:?} and {:?}", self, other);
      return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
    }
    Ok(SymBool::from(self.solver, self.address == other.address))
  }
}
