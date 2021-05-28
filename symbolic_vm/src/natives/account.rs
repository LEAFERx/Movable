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
use crate::types::{
  natives::{native_gas, SymNativeContext, SymNativeResult},
  values::{SymAccountAddress, SymValue},
};

pub fn native_create_signer<'ctx>(
  _context: &mut impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut arguments: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.is_empty());
  debug_assert!(arguments.len() == 1);

  let address = pop_arg!(arguments, SymAccountAddress);
  // let cost = native_gas(context.cost_table(), NativeCostIndex::CREATE_SIGNER, 0);
  let cost = InternalGasUnits::new(0);
  Ok(SymNativeResult::ok(cost, vec![SymValue::sym_signer(address)]))
}

pub fn native_destroy_signer<'ctx>(
  _context: &mut impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  arguments: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.is_empty());
  debug_assert!(arguments.len() == 1);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::DESTROY_SIGNER, 0);
  let cost = InternalGasUnits::new(0);
  Ok(SymNativeResult::ok(cost, vec![]))
}
