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
use z3::{ast, ast::Ast, Context};

use crate::symbolic_vm::types::{account_address::SymAccountAddress, byte_array::SymByteArray};

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
  U8(ast::BV<'ctx>),
  U64(ast::BV<'ctx>),
  U128(ast::BV<'ctx>),
  // We do not symbolify account address
  // This is only a wrapper to preserve a ref tp Z3 context
  Address(SymAccountAddress<'ctx>),
  Bool(ast::Bool<'ctx>),
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
  ctx: &'ctx Context,
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

impl<'ctx> SymValueImpl<'ctx> {
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

  fn equals(&self, v2: &SymValueImpl<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    match (self, v2) {
      // values
      (SymValueImpl::U8(u1), SymValueImpl::U8(u2)) => Ok(u1._eq(u2)),
      (SymValueImpl::U64(u1), SymValueImpl::U64(u2)) => Ok(u1._eq(u2)),
      (SymValueImpl::U128(u1), SymValueImpl::U128(u2)) => Ok(u1._eq(u2)),
      (SymValueImpl::Bool(b1), SymValueImpl::Bool(b2)) => Ok(b1._eq(b2)),
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

  pub fn from_u8(ctx: &'ctx Context, value: u8) -> Self {
    SymValue(SymValueImpl::U8(ast::BV::from_u64(ctx, value as u64, 8)))
  }

  pub fn new_u8(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U8(ast::BV::fresh_const(ctx, prefix, 8)))
  }

  pub fn from_u64(ctx: &'ctx Context, value: u64) -> Self {
    SymValue(SymValueImpl::U64(ast::BV::from_u64(ctx, value, 64)))
  }

  pub fn new_u64(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(ast::BV::fresh_const(ctx, prefix, 64)))
  }

  pub fn from_u128(ctx: &'ctx Context, value: u128) -> Self {
    let x = ast::BV::from_u64(ctx, (value >> 64) as u64, 64).concat(&ast::BV::from_u64(
      ctx,
      value as u64,
      64,
    ));
    SymValue(SymValueImpl::U128(x))
  }

  pub fn new_u128(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(ast::BV::fresh_const(ctx, prefix, 128)))
  }

  pub fn from_address(ctx: &'ctx Context, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(ctx, address)))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn from_bool(ctx: &'ctx Context, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(ast::Bool::from_bool(ctx, value)))
  }

  pub fn new_bool(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(ast::Bool::new_const(ctx, prefix)))
  }

  pub fn from_byte_array(_ctx: &'ctx Context, _bytearray: ByteArray) -> Self {
    unimplemented!()
  }

  pub fn from_sym_byte_array(bytearray: SymByteArray<'ctx>) -> Self {
    SymValue(SymValueImpl::ByteArray(bytearray))
  }

  pub fn new_byte_array(_ctx: &'ctx Context, _prefix: &str) -> Self {
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

  pub fn equals(&self, v2: &SymValue<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    self.0.equals(&v2.0)
  }

  pub fn not_equals(&self, v2: &SymValue<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    self.0.equals(&v2.0).and_then(|res| Ok(res.not()))
  }

  // Move it to SymValueImpl later
  pub fn into_ast(self) -> VMResult<ast::Dynamic<'ctx>>
  {
    match self.0 {
      SymValueImpl::U8(u) => Ok(u.into()),
      SymValueImpl::U64(u) => Ok(u.into()),
      SymValueImpl::U128(u) => Ok(u.into()),
      SymValueImpl::Bool(b) => Ok(b.into()),
      _ => {
        let msg = format!("Cannot convert {:?} to ast.", self.0);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

// Should be deleted
impl<'ctx> From<ast::BV<'ctx>> for SymValue<'ctx> {
  fn from(ast_bv: ast::BV<'ctx>) -> SymValue<'ctx> {
    match ast_bv.get_size() {
      8 => SymValue(SymValueImpl::U8(ast_bv)),
      64 => SymValue(SymValueImpl::U64(ast_bv)),
      128 => SymValue(SymValueImpl::U128(ast_bv)),
      _ => panic!(
        "Trying to implicitly convert a bitvector of size {:?} to SymValue",
        ast_bv.get_size()
      ),
    }
  }
}

// Should be deleted
impl<'ctx> From<ast::Bool<'ctx>> for SymValue<'ctx> {
  fn from(ast_bool: ast::Bool<'ctx>) -> SymValue<'ctx> {
    SymValue(SymValueImpl::Bool(ast_bool))
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<ast::BV<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<ast::BV<'ctx>> {
    match value.0 {
      SymValueImpl::U8(ast) => Ok(ast),
      SymValueImpl::U64(ast) => Ok(ast),
      SymValueImpl::U128(ast) => Ok(ast),
      _ => {
        let msg = format!("Cannot cast {:?} to ast::BV", value);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for VMResult<ast::Bool<'ctx>> {
  fn from(value: SymValue<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    match value.0 {
      SymValueImpl::Bool(ast) => Ok(ast),
      _ => {
        let msg = format!("Cannot cast {:?} to ast::BV", value);
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

  fn equals(&self, v2: &SymMutVal<'ctx>) -> VMResult<z3::ast::Bool<'ctx>> {
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
  pub fn new(ctx: &'ctx Context, values: Vec<SymValue<'ctx>>) -> Self {
    let mut fields = vec![];
    for value in values {
      fields.push(SymMutVal::new(value));
    }

    SymStruct { ctx, fields }
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
    Ok(SymValue::from_sym_struct(SymStruct::new(self.ctx, values)))
  }

  pub fn equals(&self, s2: &SymStruct<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    if self.ctx != s2.ctx {
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
    let mut res = ast::Bool::from_bool(self.ctx, true);
    for (v1, v2) in self.fields.iter().zip(&s2.fields) {
      res = res.and(&[&v1.equals(v2)?]);
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

  fn equals(&self, ref2: &SymReference<'ctx>) -> VMResult<ast::Bool<'ctx>> {
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
