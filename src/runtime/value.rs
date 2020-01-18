use libra_types::{
  // account_address::AccountAddress,
  vm_error::{StatusCode, VMStatus},
};
use std::mem::replace;
use vm::{errors::*, IndexKind, vm_string::VMStr};
use z3::{ast, ast::Ast, Context, Symbol, Sort};

// address is [u8; 32] now
// libra/types/src/account_address.rs
// const ADDRESS_BV_LENGTH: u32 = 256;

#[derive(Debug, Clone)]
enum ValueImpl<'ctx> {
  Invalid,

  U64(ast::Int<'ctx>),
  // Address(ast::BV<'ctx>), ->ast::Array?
  Bool(ast::Bool<'ctx>),
  ByteArray(ast::Array<'ctx>),
  String(ast::Array<'ctx>),

  Struct(),
  NativeStruct(),

  Reference(),
  GlobalRef(),
  PromotedRef(),
}

#[derive(Debug, Clone)]
pub struct Value<'ctx>(ValueImpl<'ctx>);

#[derive(Debug, Clone)]
pub struct Locals<'ctx>(Vec<ValueImpl<'ctx>>);

impl<'ctx> ValueImpl<'ctx> {
  fn into_value(self) -> VMResult<Value<'ctx>> {
    match self {
      ValueImpl::Invalid => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
      _ => Ok(Value(self)),
    }
  }

  fn copy_value(&self) -> VMResult<Value<'ctx>> {
    match self {
      ValueImpl::Invalid => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
      _ => Ok(Value(self.clone())),
    }
  }
  
  fn equals(self, v2: ValueImpl<'ctx>) -> VMResult<ast::Bool<'ctx>> {
    match (self, v2) {
        // values
        (ValueImpl::U64(u1), ValueImpl::U64(u2)) => Ok(u1._eq(&u2)),
        (ValueImpl::Bool(b1), ValueImpl::Bool(b2)) => Ok(b1._eq(&b2)),
        // (ValueImpl::Address(a1), ValueImpl::Address(a2)) => Ok(a1 == a2),
        // (ValueImpl::ByteArray(ba1), ValueImpl::ByteArray(ba2)) => Ok(ba1 == ba2),
        // (ValueImpl::String(s1), ValueImpl::String(s2)) => Ok(s1 == s2),
        // (ValueImpl::Struct(s1), ValueImpl::Struct(s2)) => s1.equals(s2),
        // references
        // (ValueImpl::Reference(ref1), ValueImpl::Reference(ref2)) => ref1.equals(ref2),
        // (ValueImpl::GlobalRef(gr1), ValueImpl::GlobalRef(gr2)) => gr1.equals(gr2),
        // (ValueImpl::GlobalRef(gr), ValueImpl::Reference(reference)) => gr.equals_ref(reference),
        // (ValueImpl::Reference(reference), ValueImpl::GlobalRef(gr)) => gr.equals_ref(reference),
        _ => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)),
    }
}
}

impl<'ctx> Value<'ctx> {
  // pub fn as_inner<T>(&self) -> Option<&T> {
  //   match self.0 {
  //     ValueImpl::Bool(ast) =>
  //   }
  // }

  pub fn from_u64(ctx: &'ctx Context, value: u64) -> Self {
    Value(ValueImpl::U64(ast::Int::from_u64(ctx, value)))
  }

  pub fn new_u64(ctx: &'ctx Context, prefix: &str) -> Self {
    Value(ValueImpl::U64(ast::Int::fresh_const(ctx, prefix)))
  }

  pub fn from_bool(ctx: &'ctx Context, value: bool) -> Self {
    Value(ValueImpl::Bool(ast::Bool::from_bool(ctx, value)))
  }

  pub fn new_bool(ctx: &'ctx Context, prefix: &str) -> Self {
    Value(ValueImpl::Bool(ast::Bool::new_const(ctx, prefix)))
  }

  pub fn new_string(ctx: &'ctx Context, prefix: &str) -> Self {
    Value(ValueImpl::String(ast::Array::fresh_const(
      ctx,
      prefix,
      &Sort::int(ctx),
      &Sort::bitvector(ctx, 8),
    )))
  }

  pub fn from_string<T>(ctx: &'ctx Context, value: &VMStr) -> Self {
    let bytes = value.as_bytes();
    let symbolic_string = ast::Array::fresh_const(
      ctx,
      "const_str",
      &Sort::int(ctx),
      &Sort::bitvector(ctx, 8),
    );
    for index in 0..value.len() {
      symbolic_string.store(
        &ast::Int::from_u64(ctx, index as u64).into(),
        &ast::BV::from_u64(ctx, bytes[index] as u64, 8).into(),
      );
    }
    Value(ValueImpl::String(symbolic_string))
  }

  pub fn value_as<T>(self) -> Option<T>
  where
    Option<T>: From<Value<'ctx>>,
  {
    std::convert::Into::into(self)
  }
  
  pub fn equals(self, v2: Value<'ctx>) -> VMResult<Value<'ctx>> {
    self.0.equals(v2.0).map(|res| res.into())
  }

  pub fn not_equals(self, v2: Value<'ctx>) -> VMResult<Value<'ctx>> {
    self.0.equals(v2.0).map(|res| res.not().into())
  }
}

impl<'ctx> From<ast::Int<'ctx>> for Value<'ctx> {
  fn from(ast_int: ast::Int<'ctx>) -> Value<'ctx> {
    Value(ValueImpl::U64(ast_int))
  }
}

impl<'ctx> From<ast::Bool<'ctx>> for Value<'ctx> {
  fn from(ast_bool: ast::Bool<'ctx>) -> Value<'ctx> {
    Value(ValueImpl::Bool(ast_bool))
  }
}

impl<'ctx> From<Value<'ctx>> for Option<ast::Int<'ctx>> {
  fn from(value: Value<'ctx>) -> Option<ast::Int<'ctx>> {
    match value.0 {
      ValueImpl::U64(ast) => Some(ast),
      _ => None,
    }
  }
}

impl<'ctx> From<Value<'ctx>> for Option<ast::Bool<'ctx>> {
  fn from(value: Value<'ctx>) -> Option<ast::Bool<'ctx>> {
    match value.0 {
      ValueImpl::Bool(ast) => Some(ast),
      _ => None,
    }
  }
}

impl<'ctx> From<Value<'ctx>> for Option<ast::Array<'ctx>> {
  fn from(value: Value<'ctx>) -> Option<ast::Array<'ctx>> {
    match value.0 {
      ValueImpl::String(ast) => Some(ast),
      _ => None,
    }
  }
}

impl<'ctx> Locals<'ctx> {
  pub fn new(size: usize) -> Self {
    Locals(vec![ValueImpl::Invalid; size])
  }

  pub fn copy_loc(&self, idx: usize) -> VMResult<Value<'ctx>> {
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

  pub fn move_loc(&mut self, idx: usize) -> VMResult<Value<'ctx>> {
    if let Some(local_ref) = self.0.get_mut(idx) {
      let old_local = replace(local_ref, ValueImpl::Invalid);
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

  pub fn store_loc(&mut self, idx: usize, value: Value<'ctx>) -> VMResult<()> {
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
