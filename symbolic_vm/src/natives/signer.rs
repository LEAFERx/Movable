// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_core_types::gas_schedule::{InternalGasUnits, GasAlgebra};
use move_vm_types::{
  gas_schedule::NativeCostIndex,
  loaded_data::runtime_types::Type,
};
use std::collections::VecDeque;
use vm::errors::PartialVMResult;

use crate::pop_arg;
use crate::{
  types::{
    natives::{native_gas, SymNativeContext, SymNativeResult},
    values::{SymSignerRef, SymValue},
  },
};

pub fn native_borrow_address<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  _ty_args: Vec<Type>,
  mut arguments: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(_ty_args.is_empty());
  debug_assert!(arguments.len() == 1);

  let signer_reference = pop_arg!(arguments, SymSignerRef);
  // let cost = native_gas(context.cost_table(), NativeCostIndex::SIGNER_BORROW, 1);
  let cost = InternalGasUnits::new(0);

  Ok(SymNativeResult::ok(
      cost,
      vec![signer_reference.borrow_signer()?],
  ))
}
