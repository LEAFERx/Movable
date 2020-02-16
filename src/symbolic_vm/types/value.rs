use libra_types::{
  account_address::AccountAddress,
  byte_array::ByteArray,
  vm_error::{StatusCode, VMStatus},
};
use std::{
  cell::{Ref, RefCell},
  //fmt,
  mem::replace,
  //ops::Add,
  rc::Rc,
};
use vm::{errors::*, IndexKind};
use z3::ast::Dynamic;

use crate::{
  engine::solver::Solver,
  symbolic_vm::types::{
    account_address::SymAccountAddress,
    byte_array::SymByteArray,
    primitives::{SymBool, SymU128, SymU64, SymU8},
  },
};

// address is [u8; 32] now
// libra/types/src/account_address.rs
// const ADDRESS_BV_LENGTH: u32 = 256;

// --'txn == 'ctx?--

// 2020.2.11
// for every vtxn we build a Z3 context
// currently globalref & nativestruct are not implemented

#[derive(Debug, Clone)]
enum SymValueImpl<'ctx> {
  Invalid,
  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
  // We do not symbolify account address
  // This is only a wrapper to preserve a ref tp Z3 context
  Address(SymAccountAddress<'ctx>),
  Bool(SymBool<'ctx>),
  ByteArray(SymByteArray<'ctx>),

  Struct(SymStruct<'ctx>),
  #[allow(dead_code)]
  NativeStruct(()), // !!!

  Reference(SymReference<'ctx>),
  #[allow(dead_code)]
  GlobalRef(()), // !!!
  PromotedReference(SymReference<'ctx>),
}

#[derive(Debug, Clone)]
pub struct SymValue<'ctx>(SymValueImpl<'ctx>);

#[derive(Debug, Clone)]
pub struct SymMutVal<'ctx>(Rc<RefCell<SymValueImpl<'ctx>>>);

#[derive(Debug, Clone)]
pub struct SymStruct<'ctx> {
  solver: &'ctx Solver<'ctx>,
  fields: Vec<SymMutVal<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct SymReference<'ctx>(SymMutVal<'ctx>);

#[derive(Debug, Clone)]
pub struct SymLocals<'ctx>(Vec<SymValueImpl<'ctx>>);

#[derive(Debug, Clone)]
pub enum SymReferenceValue<'ctx> {
  Reference(SymReference<'ctx>),
  //GlobalRef(SymGlobalRef),
}

// #[rustfmt::skip]
// #[allow(non_camel_case_types)]
// #[derive(Debug, Clone)]
// enum SymGlobalDataStatus {
//   CLEAN   = 0,
//   DIRTY   = 1,
//   DELETED = 2,
// }

// #[derive(Debug, Clone)]
// pub struct SymRootAccessPath {
//   status: GlobalDataStatus,
//   ap: AccessPath,
// }

// #[derive(PartialEq, Eq, Debug, Clone)]
// pub struct SymGlobalRef {
//   root: Rc<RefCell<RootAccessPath>>,
//   reference: MutVal,
// }

#[derive(Debug)]
pub enum SymIntegerValue<'ctx> {
  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
}

impl<'ctx> SymValueImpl<'ctx> {
  pub fn into_ast(self) -> VMResult<Dynamic<'ctx>> {
    match self {
      SymValueImpl::U8(u) => Ok(u.collect()),
      SymValueImpl::U64(u) => Ok(u.collect()),
      SymValueImpl::U128(u) => Ok(u.collect()),
      SymValueImpl::Bool(b) => Ok(b.collect()),
      _ => {
        let msg = format!("Cannot convert {:?} to ast.", self);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }

  fn into_value(self) -> VMResult<SymValue<'ctx>> {
    match self {
      SymValueImpl::Invalid => {
        let msg = "Cannot cast an INVALID value".to_string();
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
      SymValueImpl::PromotedReference(reference) => reference.into_value(),
      _ => Ok(SymValue(self)),
    }
  }

  fn copy_value(&self) -> VMResult<SymValue<'ctx>> {
    match self {
      SymValueImpl::Invalid => {
        let msg = "Cannot cast an INVALID value".to_string();
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
      SymValueImpl::PromotedReference(reference) => reference.copy_value(),
      SymValueImpl::Struct(s) => s.copy_value(),
      // SymValueImpl::NativeStruct(s) => s.copy_value(),
      _ => Ok(SymValue(self.clone())),
    }
  }

  fn borrow_field(&self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    match self {
      SymValueImpl::Struct(s) => s.get_field_reference(field_offset),
      _ => {
        let msg = format!("Borrow field must be called on a Struct, found {:?}", self);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }

  fn equals(&self, v2: &SymValueImpl<'ctx>) -> VMResult<SymBool<'ctx>> {
    match (self, v2) {
      // values
      (SymValueImpl::U8(u1), SymValueImpl::U8(u2)) => Ok(u1.equals(u2)),
      (SymValueImpl::U64(u1), SymValueImpl::U64(u2)) => Ok(u1.equals(u2)),
      (SymValueImpl::U128(u1), SymValueImpl::U128(u2)) => Ok(u1.equals(u2)),
      (SymValueImpl::Bool(b1), SymValueImpl::Bool(b2)) => Ok(b1.equals(b2)),
      (SymValueImpl::Address(a1), SymValueImpl::Address(a2)) => a1.equals(a2),
      (SymValueImpl::ByteArray(ba1), SymValueImpl::ByteArray(ba2)) => Ok(ba1.equals(&ba2)),
      (SymValueImpl::Struct(s1), SymValueImpl::Struct(s2)) => s1.equals(s2),
      // references
      (SymValueImpl::Reference(ref1), SymValueImpl::Reference(ref2)) => ref1.equals(ref2),
      // (SymValueImpl::GlobalRef(gr1), SymValueImpl::GlobalRef(gr2)) => gr1.equals(gr2),
      // (SymValueImpl::GlobalRef(gr), SymValueImpl::Reference(reference)) => gr.equals_ref(reference),
      // (SymValueImpl::Reference(reference), SymValueImpl::GlobalRef(gr)) => gr.equals_ref(reference),
      _ => {
        let msg = format!("Invalid equality called between {:?} and {:?}", self, v2);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  fn new(value: SymValueImpl<'ctx>) -> Self {
    SymValue(value)
  }

  pub fn from_u8(solver: &'ctx Solver, value: u8) -> Self {
    SymValue(SymValueImpl::U8(SymU8::from(solver, value)))
  }

  pub fn from_sym_u8(sym: SymU8<'ctx>) -> Self {
    SymValue(SymValueImpl::U8(sym))
  }

  pub fn new_u8(solver: &'ctx Solver, prefix: &str) -> Self {
    SymValue(SymValueImpl::U8(SymU8::new(solver, prefix)))
  }

  pub fn from_u64(solver: &'ctx Solver, value: u64) -> Self {
    SymValue(SymValueImpl::U64(SymU64::from(solver, value)))
  }

  pub fn from_sym_u64(sym: SymU64<'ctx>) -> Self {
    SymValue(SymValueImpl::U64(sym))
  }

  pub fn new_u64(solver: &'ctx Solver, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(SymU64::new(solver, prefix)))
  }

  pub fn from_u128(solver: &'ctx Solver, value: u128) -> Self {
    SymValue(SymValueImpl::U128(SymU128::from(solver, value)))
  }

  pub fn from_sym_u128(sym: SymU128<'ctx>) -> Self {
    SymValue(SymValueImpl::U128(sym))
  }

  pub fn new_u128(solver: &'ctx Solver, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(SymU128::new(solver, prefix)))
  }

  pub fn from_address(solver: &'ctx Solver, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(
      solver, address,
    )))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn from_bool(solver: &'ctx Solver, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::from(solver, value)))
  }

  pub fn from_sym_bool(sym: SymBool<'ctx>) -> Self {
    SymValue(SymValueImpl::Bool(sym))
  }

  pub fn new_bool(solver: &'ctx Solver, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::new(solver, prefix)))
  }

  pub fn from_byte_array(_solver: &'ctx Solver, _bytearray: ByteArray) -> Self {
    unimplemented!()
  }

  pub fn from_sym_byte_array(bytearray: SymByteArray<'ctx>) -> Self {
    SymValue(SymValueImpl::ByteArray(bytearray))
  }

  pub fn new_byte_array(_solver: &'ctx Solver, _prefix: &str) -> Self {
    unimplemented!()
  }

  pub fn from_sym_struct(s: SymStruct<'ctx>) -> Self {
    SymValue(SymValueImpl::Struct(s))
  }

  pub fn from_sym_reference(reference: SymReference<'ctx>) -> Self {
    SymValue(SymValueImpl::Reference(reference))
  }

  // global_reference

  // native_struct

  pub fn value_as<T>(self) -> VMResult<T>
  where
    VMResult<T>: From<SymValue<'ctx>>,
  {
    std::convert::Into::into(self)
  }

  pub fn equals(&self, v2: &SymValue<'ctx>) -> VMResult<SymBool<'ctx>> {
    self.0.equals(&v2.0)
  }

  pub fn not_equals(&self, v2: &SymValue<'ctx>) -> VMResult<SymBool<'ctx>> {
    self.0.equals(&v2.0).and_then(|res| Ok(res.not()))
  }

  // Move it to SymValueImpl later
  pub fn into_ast(self) -> VMResult<Dynamic<'ctx>> {
    self.0.into_ast()
  }
}

impl<'ctx> SymIntegerValue<'ctx> {
  pub fn add(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::add(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::add(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::add(l, r))),
      (l, r) => {
        let msg = format!("Cannot add {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn sub(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::sub(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::sub(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::sub(l, r))),
      (l, r) => {
        let msg = format!("Cannot sub {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn mul(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::mul(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::mul(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::mul(l, r))),
      (l, r) => {
        let msg = format!("Cannot mul {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn div(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::div(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::div(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::div(l, r))),
      (l, r) => {
        let msg = format!("Cannot div {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn rem(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::rem(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::rem(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::rem(l, r))),
      (l, r) => {
        let msg = format!("Cannot rem {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn bit_or(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_or(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_or(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_or(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_or {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_and(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_and(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_and(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_and(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_and {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_xor(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_xor(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_xor(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_xor(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_xor {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn shl(self, n_bits: SymU8<'ctx>) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shl(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shl(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shl(&n_bits)),
    })
  }

  pub fn shr(self, n_bits: SymU8<'ctx>) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shr(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shr(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shr(&n_bits)),
    })
  }

  pub fn lt(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::lt(l, r),
      (U64(l), U64(r)) => SymU64::lt(l, r),
      (U128(l), U128(r)) => SymU128::lt(l, r),
      (l, r) => {
        let msg = format!("Cannot lt {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn le(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::le(l, r),
      (U64(l), U64(r)) => SymU64::le(l, r),
      (U128(l), U128(r)) => SymU128::le(l, r),
      (l, r) => {
        let msg = format!("Cannot le {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn gt(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::gt(l, r),
      (U64(l), U64(r)) => SymU64::gt(l, r),
      (U128(l), U128(r)) => SymU128::gt(l, r),
      (l, r) => {
        let msg = format!("Cannot gt {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn ge(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::ge(l, r),
      (U64(l), U64(r)) => SymU64::ge(l, r),
      (U128(l), U128(r)) => SymU128::ge(l, r),
      (l, r) => {
        let msg = format!("Cannot ge {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn into_value(self) -> SymValue<'ctx> {
    use SymIntegerValue::*;

    match self {
      U8(x) => SymValue::from_sym_u8(x),
      U64(x) => SymValue::from_sym_u64(x),
      U128(x) => SymValue::from_sym_u128(x),
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<SymU8<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<SymU8<'ctx>> {
    match value.0 {
      SymValueImpl::U8(u) => Ok(u),
      _ => {
        let msg = format!("Cannot cast {:?} to SymU8", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<SymU64<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<SymU64<'ctx>> {
    match value.0 {
      SymValueImpl::U64(u) => Ok(u),
      _ => {
        let msg = format!("Cannot cast {:?} to SymU64", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<SymU128<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<SymU128<'ctx>> {
    match value.0 {
      SymValueImpl::U128(u) => Ok(u),
      _ => {
        let msg = format!("Cannot cast {:?} to SymU128", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<SymIntegerValue<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<SymIntegerValue<'ctx>> {
    match value.0 {
      SymValueImpl::U8(i) => Ok(SymIntegerValue::U8(i)),
      SymValueImpl::U64(i) => Ok(SymIntegerValue::U64(i)),
      SymValueImpl::U128(i) => Ok(SymIntegerValue::U128(i)),
      _ => {
        let msg = format!("Cannot cast {:?} to integer", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<SymBool<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<SymBool<'ctx>> {
    match value.0 {
      SymValueImpl::Bool(b) => Ok(b),
      _ => {
        let msg = format!("Cannot cast {:?} to SymBool", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> SymMutVal<'ctx> {
  pub fn new(v: SymValue<'ctx>) -> Self {
    SymMutVal(Rc::new(RefCell::new(v.0)))
  }

  fn peek(&self) -> Ref<SymValueImpl<'ctx>> {
    self.0.borrow()
  }

  pub fn into_value(self) -> VMResult<SymValue<'ctx>> {
    match Rc::try_unwrap(self.0) {
      Ok(cell) => Ok(SymValue::new(cell.into_inner())),
      Err(_) => Err(VMStatus::new(StatusCode::LOCAL_REFERENCE_ERROR)),
    }
  }

  pub fn copy_value(&self) -> VMResult<SymValue<'ctx>> {
    self.peek().copy_value()
  }

  // pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
  //   self.peek().size()
  // }

  fn borrow_field(&self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    self.peek().borrow_field(field_offset)
  }

  fn write_value(self, value: SymValue<'ctx>) {
    self.0.replace(value.0);
  }

  fn equals(&self, v2: &SymMutVal<'ctx>) -> VMResult<SymBool<'ctx>> {
    self.peek().equals(&v2.peek())
  }

  // fn mutate_native_struct<T, F>(&self, op: F) -> VMResult<T>
  // where
  //   F: FnOnce(&mut NativeStructValue) -> VMResult<T>,
  // {
  //   match &mut *self.0.borrow_mut() {
  //     ValueImpl::NativeStruct(s) => op(s),
  //     _ => {
  //       let msg = format!("Cannot cast {:?} to NativeStruct", self);
  //       Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
  //     }
  //   }
  // }

  // fn read_native_struct<T, F>(&self, op: F) -> VMResult<T>
  // where
  //   F: FnOnce(&NativeStructValue) -> VMResult<T>,
  // {
  //   match &*self.0.borrow_mut() {
  //     ValueImpl::NativeStruct(s) => op(s),
  //     _ => {
  //       let msg = format!("Cannot cast {:?} to NativeStruct", self);
  //       Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
  //     }
  //   }
  // }

  // fn pretty_string(&self) -> String {
  //   self.peek().pretty_string()
  // }
}

impl<'ctx> SymStruct<'ctx> {
  pub fn new(solver: &'ctx Solver<'ctx>, values: Vec<SymValue<'ctx>>) -> Self {
    let mut fields = vec![];
    for value in values {
      fields.push(SymMutVal::new(value));
    }

    SymStruct { solver, fields }
  }
  pub fn get_field_value(&self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    if let Some(field_ref) = self.fields.get(field_offset) {
      field_ref.copy_value()
    } else {
      let msg = format!("Invalid field at index {} for {:?}", field_offset, self);
      Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
    }
  }

  pub fn get_field_reference(&self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    if let Some(field_ref) = self.fields.get(field_offset) {
      Ok(SymValue::from_sym_reference(SymReference(
        field_ref.clone(),
      )))
    } else {
      let msg = format!("Invalid field at index {} for {:?}", field_offset, self);
      Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
    }
  }

  fn copy_value(&self) -> VMResult<SymValue<'ctx>> {
    let mut values: Vec<SymValue<'ctx>> = vec![];
    for value in &self.fields {
      values.push(value.copy_value()?);
    }
    Ok(SymValue::from_sym_struct(SymStruct::new(
      self.solver,
      values,
    )))
  }

  pub fn equals(&self, s2: &SymStruct<'ctx>) -> VMResult<SymBool<'ctx>> {
    if self.solver != s2.solver {
      let msg = format!(
        "Equals on struct with different context: {:?} and {:?}",
        self, s2
      );
      return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
    }
    if self.fields.len() != s2.fields.len() {
      let msg = format!("Equals on different types {:?} for {:?}", self, s2);
      return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
    }
    let mut res = SymBool::from(self.solver, true);
    for (v1, v2) in self.fields.iter().zip(&s2.fields) {
      res = res.and(&v1.equals(v2)?);
    }
    Ok(res)
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn new(value: SymValue<'ctx>) -> Self {
    SymReference(SymMutVal::new(value))
  }

  #[allow(dead_code)]
  fn new_from_cell(val: SymMutVal<'ctx>) -> Self {
    SymReference(val)
  }

  fn into_value(self) -> VMResult<SymValue<'ctx>> {
    self.0.into_value()
  }

  fn copy_value(&self) -> VMResult<SymValue<'ctx>> {
    self.0.copy_value()
  }

  fn borrow_field(&self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    self.0.borrow_field(field_offset)
  }

  fn write_value(self, value: SymValue<'ctx>) {
    self.0.write_value(value);
  }

  fn equals(&self, ref2: &SymReference<'ctx>) -> VMResult<SymBool<'ctx>> {
    self.0.equals(&ref2.0)
  }
}

impl<'ctx> SymReferenceValue<'ctx> {
  pub fn new(value: SymValue<'ctx>) -> VMResult<Self> {
    match value.0 {
      SymValueImpl::Reference(reference) => Ok(SymReferenceValue::Reference(reference)),
      // SymValueImpl::GlobalRef(reference) => Ok(SymReferenceValue::GlobalRef(reference)),
      _ => {
        let msg = format!("ReferenceValue must be built from a reference {:?}", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }

  pub fn borrow_field(self, field_offset: usize) -> VMResult<SymValue<'ctx>> {
    match self {
      // SymReferenceValue::GlobalRef(ref reference) => reference.borrow_field(field_offset),
      SymReferenceValue::Reference(ref reference) => reference.borrow_field(field_offset),
    }
  }

  pub fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    match self {
      // SymReferenceValue::GlobalRef(reference) => reference.copy_value(),
      SymReferenceValue::Reference(reference) => reference.copy_value(),
    }
  }

  pub fn write_ref(self, value: SymValue<'ctx>) {
    match self {
      // SymReferenceValue::GlobalRef(reference) => reference.write_value(value),
      SymReferenceValue::Reference(reference) => reference.write_value(value),
    }
  }

  // #[allow(dead_code)]
  // pub(crate) fn mutate_native_struct<T, F>(&self, op: F) -> VMResult<T>
  // where
  //   F: FnOnce(&mut NativeStructValue) -> VMResult<T>,
  // {
  //   match self {
  //     ReferenceValue::GlobalRef(reference) => reference.mutate_native_struct(op),
  //     ReferenceValue::Reference(reference) => reference.mutate_native_struct(op),
  //   }
  // }

  // pub(crate) fn read_native_struct<T, F>(&self, op: F) -> VMResult<T>
  // where
  //   F: FnOnce(&NativeStructValue) -> VMResult<T>,
  // {
  //   match self {
  //     ReferenceValue::GlobalRef(reference) => reference.read_native_struct(op),
  //     ReferenceValue::Reference(reference) => reference.read_native_struct(op),
  //   }
  // }

  // pub(crate) fn get_native_struct_reference<F>(&self, op: F) -> VMResult<Value>
  // where
  //   F: FnOnce(&NativeStructValue) -> VMResult<MutVal>,
  // {
  //   match self {
  //     ReferenceValue::GlobalRef(reference) => reference
  //       .read_native_struct(op)
  //       .map(|v| Value::global_ref(GlobalRef::new_ref(reference, v))),
  //     ReferenceValue::Reference(reference) => reference
  //       .read_native_struct(op)
  //       .map(|v| Value::reference(Reference::new_from_cell(v))),
  //   }
  // }
}

impl<'ctx> SymLocals<'ctx> {
  pub fn new(size: usize) -> Self {
    SymLocals(vec![SymValueImpl::Invalid; size])
  }

  pub fn copy_loc(&self, idx: usize) -> VMResult<SymValue<'ctx>> {
    if let Some(local_ref) = self.0.get(idx) {
      local_ref.copy_value()
    } else {
      let msg = format!(
        "Index {} out of bounds for {} while indexing {}",
        idx,
        self.0.len(),
        IndexKind::LocalPool
      );
      Err(VMStatus::new(StatusCode::INDEX_OUT_OF_BOUNDS).with_message(msg))
    }
  }

  pub fn move_loc(&mut self, idx: usize) -> VMResult<SymValue<'ctx>> {
    if let Some(local_ref) = self.0.get_mut(idx) {
      let old_local = replace(local_ref, SymValueImpl::Invalid);
      old_local.into_value()
    } else {
      let msg = format!(
        "Index {} out of bounds for {} while indexing {}",
        idx,
        self.0.len(),
        IndexKind::LocalPool
      );
      Err(VMStatus::new(StatusCode::INDEX_OUT_OF_BOUNDS).with_message(msg))
    }
  }

  pub fn store_loc(&mut self, idx: usize, value: SymValue<'ctx>) -> VMResult<()> {
    if let Some(local_ref) = self.0.get_mut(idx) {
      replace(local_ref, value.0);
      Ok(())
    } else {
      let msg = format!(
        "Index {} out of bounds for {} while indexing {}",
        idx,
        self.0.len(),
        IndexKind::LocalPool
      );
      Err(VMStatus::new(StatusCode::INDEX_OUT_OF_BOUNDS).with_message(msg))
    }
  }

  pub fn borrow_loc(&mut self, idx: usize) -> VMResult<SymValue<'ctx>> {
    if let Some(local_ref) = self.0.get_mut(idx) {
      match local_ref {
        SymValueImpl::GlobalRef(_) | SymValueImpl::Reference(_) | SymValueImpl::Invalid => {
          let msg = format!(
            "BorrowLoc on an invalid local {:?} at index {}",
            local_ref, idx
          );
          Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
        }
        SymValueImpl::PromotedReference(reference) => {
          Ok(SymValue::from_sym_reference(reference.clone()))
        }
        _ => {
          let ref_value = SymMutVal::new(SymValue::new(local_ref.clone()));
          let new_local_ref = SymValueImpl::PromotedReference(SymReference(ref_value.clone()));
          replace(local_ref, new_local_ref);
          Ok(SymValue::from_sym_reference(SymReference(ref_value)))
        }
      }
    } else {
      let msg = format!(
        "Index {} out of bounds for {} while indexing {}",
        idx,
        self.0.len(),
        IndexKind::LocalPool
      );
      Err(VMStatus::new(StatusCode::INDEX_OUT_OF_BOUNDS).with_message(msg))
    }
  }
}
