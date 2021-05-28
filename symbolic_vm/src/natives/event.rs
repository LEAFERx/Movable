// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_core_types::gas_schedule::{InternalGasUnits, GasAlgebra};
use move_vm_types::{
  gas_schedule::NativeCostIndex,
  loaded_data::runtime_types::Type,
  natives::function::{native_gas, NativeContext, NativeResult},
  values::Value,
};
use std::collections::VecDeque;
use vm::errors::PartialVMResult;

use crate::pop_arg;
use crate::types::{
  natives::{native_gas, SymNativeContext, SymNativeResult},
  values::{SymU64, SymVector, SymValue},
};

pub fn native_emit_event<'ctx>(
  context: &mut impl SymNativeContext<'ctx>,
  mut ty_args: Vec<Type>,
  mut arguments: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(arguments.len() == 3);

  let ty = ty_args.pop().unwrap();
  let msg = arguments.pop_back().unwrap();
  // let seq_num = pop_arg!(arguments, u64);
  // let guid = pop_arg!(arguments, Vec<u8>);

  // let cost = native_gas(
  //   context.cost_table(),
  //   NativeCostIndex::EMIT_EVENT,
  //   msg.size().get() as usize,
  // );
  let cost = InternalGasUnits::new(0);

  if !context.save_event(guid, seq_num, ty, msg)? {
    return Ok(SymNativeResult::err(cost, 0));
  }

  Ok(SymNativeResult::ok(cost, smallvec![]))
}
