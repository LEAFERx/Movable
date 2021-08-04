use vm::{
  errors::*,
};

use z3::{
  ast::{Ast, Bool, Dynamic, BV},
  Context,
};

use std::fmt;

use super::SymbolicMoveValue;
use crate::runtime::context::TypeContext;

#[derive(Debug, Clone)]
pub struct SymU8<'ctx> {
  ast: BV<'ctx>,
}

#[derive(Debug, Clone)]
pub struct SymU64<'ctx> {
  ast: BV<'ctx>,
}

#[derive(Debug, Clone)]
pub struct SymU128<'ctx> {
  ast: BV<'ctx>,
}

#[derive(Debug, Clone)]
pub struct SymBool<'ctx> {
  ast: Bool<'ctx>,
}

// Consider to use a macro to do impl

impl<'ctx> SymU8<'ctx> {
  pub fn from(z3_ctx: &'ctx Context, value: u8) -> Self {
    SymU8 {
      ast: BV::from_u64(z3_ctx, value as u64, 8),
    }
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 8);
    SymU8 { ast }
  }

  pub fn new(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymU8 {
      ast: BV::fresh_const(z3_ctx, prefix, 8),
    }
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.ast.zero_ext(64 - 8))
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.ast.zero_ext(128 - 8))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast._eq(&other.ast),
    }
  }

  pub fn add(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvadd(&other.ast),
    }
  }

  pub fn sub(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvsub(&other.ast),
    }
  }

  pub fn mul(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvmul(&other.ast),
    }
  }

  pub fn div(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvudiv(&other.ast),
    }
  }

  pub fn rem(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvurem(&other.ast),
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvor(&other.ast),
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvand(&other.ast),
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvxor(&other.ast),
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvshl(&n_bits.ast),
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    SymU8 {
      ast: self.ast.bvlshr(&n_bits.ast),
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvult(&other.ast),
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvule(&other.ast),
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvugt(&other.ast),
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvuge(&other.ast),
    }
  }
}

impl<'ctx> SymU64<'ctx> {
  pub fn from(z3_ctx: &'ctx Context, value: u64) -> Self {
    SymU64 {
      ast: BV::from_u64(z3_ctx, value, 64),
    }
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 64);
    SymU64 { ast }
  }

  pub fn new(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymU64 {
      ast: BV::fresh_const(z3_ctx, prefix, 64),
    }
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.ast.extract(7, 0))
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.ast.zero_ext(128 - 64))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast._eq(&other.ast),
    }
  }

  pub fn add(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvadd(&other.ast),
    }
  }

  pub fn sub(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvsub(&other.ast),
    }
  }

  pub fn mul(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvmul(&other.ast),
    }
  }

  pub fn div(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvudiv(&other.ast),
    }
  }

  pub fn rem(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvurem(&other.ast),
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvor(&other.ast),
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvand(&other.ast),
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvxor(&other.ast),
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvshl(&n_bits.ast.zero_ext(64 - 8)),
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    SymU64 {
      ast: self.ast.bvlshr(&n_bits.ast.zero_ext(64 - 8)),
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvult(&other.ast),
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvule(&other.ast),
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvugt(&other.ast),
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvuge(&other.ast),
    }
  }
}

impl<'ctx> SymU128<'ctx> {
  pub fn from(z3_ctx: &'ctx Context, value: u128) -> Self {
    let ctx = z3_ctx;
    let ast =
      BV::from_u64(ctx, (value >> 64) as u64, 64).concat(&BV::from_u64(ctx, value as u64, 64));
    SymU128 { ast }
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 128);
    SymU128 { ast }
  }

  pub fn new(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymU128 {
      ast: BV::fresh_const(z3_ctx, prefix, 128),
    }
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.ast.extract(7, 0))
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.ast.extract(63, 0))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast._eq(&other.ast),
    }
  }

  pub fn add(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvadd(&other.ast),
    }
  }

  pub fn sub(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvsub(&other.ast),
    }
  }

  pub fn mul(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvmul(&other.ast),
    }
  }

  pub fn div(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvudiv(&other.ast),
    }
  }

  pub fn rem(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvurem(&other.ast),
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvor(&other.ast),
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvand(&other.ast),
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvxor(&other.ast),
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvshl(&n_bits.ast.zero_ext(128 - 8)),
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    SymU128 {
      ast: self.ast.bvlshr(&n_bits.ast.zero_ext(128 - 8)),
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvult(&other.ast),
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvule(&other.ast),
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvugt(&other.ast),
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.bvuge(&other.ast),
    }
  }
}

impl<'ctx> SymBool<'ctx> {
  pub fn from(z3_ctx: &'ctx Context, value: bool) -> Self {
    SymBool {
      ast: Bool::from_bool(z3_ctx, value),
    }
  }

  pub fn from_ast(ast: Bool<'ctx>) -> Self {
    SymBool { ast }
  }

  pub fn new(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymBool {
      ast: Bool::fresh_const(z3_ctx, prefix),
    }
  }

  pub fn as_inner(&self) -> &Bool<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast._eq(&other.ast),
    }
  }

  pub fn not(&self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.not(),
    }
  }

  pub fn and(z3_ctx: &'ctx Context, asts: &[SymBool<'ctx>]) -> SymBool<'ctx> {
    SymBool {
      ast: Bool::and(z3_ctx, &asts.iter().map(|v| &v.ast).collect::<Vec<_>>()),
    }
  }

  pub fn or(z3_ctx: &'ctx Context, asts: &[SymBool<'ctx>]) -> SymBool<'ctx> {
    SymBool {
      ast: Bool::or(z3_ctx, &asts.iter().map(|v| &v.ast).collect::<Vec<_>>()),
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU8<'ctx> {
  fn as_runtime_ast(&self, _ty_ctx: &TypeContext<'ctx>) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU64<'ctx> {
  fn as_runtime_ast(&self, _ty_ctx: &TypeContext<'ctx>) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU128<'ctx> {
  fn as_runtime_ast(&self, _ty_ctx: &TypeContext<'ctx>) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymBool<'ctx> {
  fn as_runtime_ast(&self, _ty_ctx: &TypeContext<'ctx>) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> fmt::Display for SymU8<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "SymU8({:?})", self.ast)
  }
}

impl<'ctx> fmt::Display for SymU64<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "SymU64({:?})", self.ast)
  }
}

impl<'ctx> fmt::Display for SymU128<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "SymU128({:?})", self.ast)
  }
}

impl<'ctx> fmt::Display for SymBool<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "SymBool({:?})", self.ast)
  }
}