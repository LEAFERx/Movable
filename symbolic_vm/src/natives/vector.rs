// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use move_core_types::gas_schedule::{InternalGasUnits, GasAlgebra};
use move_vm_types::{
  gas_schedule::NativeCostIndex,
  loaded_data::runtime_types::Type,
};
use std::collections::VecDeque;
use vm::errors::PartialVMResult;

use crate::{
  types::{
    natives::{native_gas, SymNativeContext, SymNativeResult},
    values::{SymU64, SymValue, SymVector, SymVectorRef},
  },
  pop_arg,
};

pub fn native_empty<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.is_empty());

  // let cost = native_gas(context.cost_table(), NativeCostIndex::EMPTY, 1);
  let cost = InternalGasUnits::new(0);
  SymVector::empty(cost, &ty_args[0], context)
}

pub fn native_length<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);

  let r = pop_arg!(args, SymVectorRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::LENGTH, 1);
  let cost = InternalGasUnits::new(0);

  let len = r.len(&ty_args[0], context)?;
  Ok(SymNativeResult::ok(cost, vec![len]))
}

pub fn native_push_back<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 2);

  let e = args.pop_back().unwrap();
  let r = pop_arg!(args, SymVectorRef);

  // let cost = native_gas(
  //   context.cost_table(),
  //   NativeCostIndex::PUSH_BACK,
  //   e.size().get() as usize,
  // );
  let cost = InternalGasUnits::new(0);

  r.push_back(e, &ty_args[0], context)?;
  Ok(SymNativeResult::ok(cost, vec![]))
}

pub fn native_borrow<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 2);

  let idx = pop_arg!(args, SymU64);
  let r = pop_arg!(args, SymVectorRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::BORROW, 1);
  let cost = InternalGasUnits::new(0);

  r.borrow_elem(idx, cost, &ty_args[0], context)
}

pub fn native_pop<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);

  let r = pop_arg!(args, SymVectorRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::POP_BACK, 1);
  let cost = InternalGasUnits::new(0);

  r.pop(cost, &ty_args[0], context)
}

pub fn native_destroy_empty<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);

  let v = pop_arg!(args, SymVector);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::DESTROY_EMPTY, 1);
  let cost = InternalGasUnits::new(0);

  v.destroy_empty(cost, &ty_args[0], context)
}

pub fn native_swap<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> PartialVMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 3);

  let idx2 = pop_arg!(args, SymU64);
  let idx1 = pop_arg!(args, SymU64);
  let r = pop_arg!(args, SymVectorRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::SWAP, 1);
  let cost = InternalGasUnits::new(0);

  r.swap(idx1, idx2, cost, &ty_args[0], context)
}
