use libra_types::{
  // account_address::AccountAddress,
  vm_error::{StatusCode, VMStatus},
};
use std::mem::replace;
use vm::{errors::*, IndexKind};
use z3::{ast, ast::Ast, Context};

// address is [u8; 32] now
// libra/types/src/account_address.rs
// const ADDRESS_BV_LENGTH: u32 = 256;

// 'txn == 'ctx?

#[derive(Debug, Clone)]
enum SymValueImpl<'ctx> {
  Invalid,
  
  U8(ast::BV<'ctx>),
  U64(ast::BV<'ctx>),
  U128(ast::BV<'ctx>),
  // Address(ast::BV<'ctx>), ->ast::Array?
  Bool(ast::Bool<'ctx>),
  ByteArray(ast::Array<'ctx>),

  Struct(),
  NativeStruct(),

  Reference(),
  GlobalRef(),
  PromotedReference(),
}

#[derive(Debug, Clone)]
pub struct SymValue<'ctx>(SymValueImpl<'ctx>);

#[derive(Debug, Clone)]
pub struct SymLocals<'ctx>(Vec<SymValueImpl<'ctx>>);

impl<'ctx> SymValueImpl<'ctx> {
  fn into_value(self) -> VMResult<SymValue<'ctx>> {
    match self {
      SymValueImpl::Invalid => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
      _ => Ok(SymValue(self)),
    }
  }

  fn copy_value(&self) -> VMResult<SymValue<'ctx>> {
    match self {
      SymValueImpl::Invalid => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
      _ => Ok(SymValue(self.clone())),
    }
  }
  
  fn equals(self, v2: SymValueImpl<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    match (self, v2) {
        // values
        (SymValueImpl::U8(u1), SymValueImpl::U8(u2)) => Ok(u1._eq(&u2)),
        (SymValueImpl::U64(u1), SymValueImpl::U64(u2)) => Ok(u1._eq(&u2)),
        (SymValueImpl::U128(u1), SymValueImpl::U128(u2)) => Ok(u1._eq(&u2)),
        (SymValueImpl::Bool(b1), SymValueImpl::Bool(b2)) => Ok(b1._eq(&b2)),
        // (SymValueImpl::Address(a1), SymValueImpl::Address(a2)) => Ok(a1 == a2),
        // (SymValueImpl::ByteArray(ba1), SymValueImpl::ByteArray(ba2)) => Ok(ba1 == ba2),
        // (SymValueImpl::String(s1), SymValueImpl::String(s2)) => Ok(s1 == s2),
        // (SymValueImpl::Struct(s1), SymValueImpl::Struct(s2)) => s1.equals(s2),
        // references
        // (SymValueImpl::Reference(ref1), SymValueImpl::Reference(ref2)) => ref1.equals(ref2),
        // (SymValueImpl::GlobalRef(gr1), SymValueImpl::GlobalRef(gr2)) => gr1.equals(gr2),
        // (SymValueImpl::GlobalRef(gr), SymValueImpl::Reference(reference)) => gr.equals_ref(reference),
        // (SymValueImpl::Reference(reference), SymValueImpl::GlobalRef(gr)) => gr.equals_ref(reference),
        _ => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
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
    SymValue(SymValueImpl::U64(ast::BV::fresh_const(ctx, prefix, 8)))
  }

  pub fn from_u64(ctx: &'ctx Context, value: u64) -> Self {
    SymValue(SymValueImpl::U64(ast::BV::from_u64(ctx, value, 64)))
  }

  pub fn new_u64(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(ast::BV::fresh_const(ctx, prefix, 64)))
  }

  pub fn from_u128(ctx: &'ctx Context, value: u128) -> Self {
    let x = ast::BV::from_u64(ctx, (value >> 64) as u64, 64)
      .concat(&ast::BV::from_u64(ctx, value as u64, 64));
    SymValue(SymValueImpl::U128(x))
  }

  pub fn new_u128(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(ast::BV::fresh_const(ctx, prefix, 128)))
  }

  pub fn from_bool(ctx: &'ctx Context, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(ast::Bool::from_bool(ctx, value)))
  }

  pub fn new_bool(ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(ast::Bool::new_const(ctx, prefix)))
  }

  pub fn value_as<T>(self) -> Option<T>
  where
    Option<T>: From<SymValue<'ctx>>,
  {
    std::convert::Into::into(self)
  }
  
  pub fn equals(self, v2: SymValue<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    self.0.equals(v2.0)
  }

  pub fn not_equals(self, v2: SymValue<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    self.0.equals(v2.0).and_then(|res| Ok(res.not()))
  }
}

impl<'ctx> From<ast::BV<'ctx>> for SymValue<'ctx> {
  fn from(ast_bv: ast::BV<'ctx>) -> SymValue<'ctx> {
    match ast_bv.get_size() {
      8 => SymValue(SymValueImpl::U8(ast_bv)),
      64 => SymValue(SymValueImpl::U8(ast_bv)),
      128 => SymValue(SymValueImpl::U8(ast_bv)),
      _ => panic!("Trying to implicitly convert a bitvector of size {:?} to SymValue", ast_bv.get_size()),
    }
  }
}

impl<'ctx> From<ast::Bool<'ctx>> for SymValue<'ctx> {
  fn from(ast_bool: ast::Bool<'ctx>) -> SymValue<'ctx> {
    SymValue(SymValueImpl::Bool(ast_bool))
  }
}

impl<'ctx> From<SymValue<'ctx>> for Option<ast::BV<'ctx>> {
  fn from(value: SymValue<'ctx>) -> Option<ast::BV<'ctx>> {
    match value.0 {
      SymValueImpl::U8(ast) => Some(ast),
      SymValueImpl::U64(ast) => Some(ast),
      SymValueImpl::U128(ast) => Some(ast),
      _ => None,
    }
  }
}

impl<'ctx> From<SymValue<'ctx>> for Option<ast::Bool<'ctx>> {
  fn from(value: SymValue<'ctx>) -> Option<ast::Bool<'ctx>> {
    match value.0 {
      SymValueImpl::Bool(ast) => Some(ast),
      _ => None,
    }
  }
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
}
