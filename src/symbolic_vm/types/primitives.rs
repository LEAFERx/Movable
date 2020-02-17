use z3::ast::{Ast, Bool, Dynamic, BV};

use crate::{engine::solver::Solver};

#[derive(Debug, Clone)]
pub struct SymU8<'ctx>(BV<'ctx>);
#[derive(Debug, Clone)]
pub struct SymU64<'ctx>(BV<'ctx>);
#[derive(Debug, Clone)]
pub struct SymU128<'ctx>(BV<'ctx>);
#[derive(Debug, Clone)]
pub struct SymBool<'ctx>(Bool<'ctx>);

// Consider to use a macro to do impl

impl<'ctx> SymU8<'ctx> {
  pub fn from(solver: &'ctx Solver, value: u8) -> Self {
    SymU8(BV::from_u64(solver.ctx(), value as u64, 8))
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 8);
    SymU8(ast)
  }

  pub fn new(solver: &'ctx Solver, prefix: &str) -> Self {
    SymU8(BV::fresh_const(solver.ctx(), prefix, 8))
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.0.zero_ext(64 - 8))
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.0.zero_ext(128 - 8))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.0
  }

  // Should drop self after collected?
  pub fn collect(self) -> Dynamic<'ctx> {
    Dynamic::from_ast(&self.0)
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0._eq(&other.0))
  }

  pub fn add(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvadd(&other.0))
  }

  pub fn sub(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvsub(&other.0))
  }

  pub fn mul(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvmul(&other.0))
  }

  pub fn div(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvudiv(&other.0))
  }

  pub fn rem(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvurem(&other.0))
  }

  pub fn bit_or(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvor(&other.0))
  }

  pub fn bit_and(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvand(&other.0))
  }

  pub fn bit_xor(&self, other: &Self) -> SymU8<'ctx> {
    SymU8(self.0.bvxor(&other.0))
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    SymU8(self.0.bvshl(&n_bits.0))
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    SymU8(self.0.bvlshr(&n_bits.0))
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvult(&other.0))
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvule(&other.0))
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvugt(&other.0))
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvuge(&other.0))
  }
}

impl<'ctx> SymU64<'ctx> {
  pub fn from(solver: &'ctx Solver, value: u64) -> Self {
    SymU64(BV::from_u64(solver.ctx(), value, 64))
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 64);
    SymU64(ast)
  }

  pub fn new(solver: &'ctx Solver, prefix: &str) -> Self {
    SymU64(BV::fresh_const(solver.ctx(), prefix, 64))
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.0.extract(7, 0))
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.0.zero_ext(128 - 64))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.0
  }

  pub fn collect(self) -> Dynamic<'ctx> {
    Dynamic::from_ast(&self.0)
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0._eq(&other.0))
  }

  pub fn add(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvadd(&other.0))
  }

  pub fn sub(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvsub(&other.0))
  }

  pub fn mul(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvmul(&other.0))
  }

  pub fn div(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvudiv(&other.0))
  }

  pub fn rem(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvurem(&other.0))
  }

  pub fn bit_or(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvor(&other.0))
  }

  pub fn bit_and(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvand(&other.0))
  }

  pub fn bit_xor(&self, other: &Self) -> SymU64<'ctx> {
    SymU64(self.0.bvxor(&other.0))
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    SymU64(self.0.bvshl(&n_bits.0))
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    SymU64(self.0.bvlshr(&n_bits.0))
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvult(&other.0))
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvule(&other.0))
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvugt(&other.0))
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvuge(&other.0))
  }
}

impl<'ctx> SymU128<'ctx> {
  pub fn from(solver: &'ctx Solver, value: u128) -> Self {
    let ctx = solver.ctx();
    let x =
      BV::from_u64(ctx, (value >> 64) as u64, 64).concat(&BV::from_u64(ctx, value as u64, 64));
    SymU128(x)
  }

  pub fn from_ast(ast: BV<'ctx>) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 128);
    SymU128(ast)
  }

  pub fn new(solver: &'ctx Solver, prefix: &str) -> Self {
    SymU128(BV::fresh_const(solver.ctx(), prefix, 128))
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.0.extract(7, 0))
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.0.extract(63, 0))
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.0
  }

  pub fn collect(self) -> Dynamic<'ctx> {
    Dynamic::from_ast(&self.0)
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0._eq(&other.0))
  }

  pub fn add(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvadd(&other.0))
  }

  pub fn sub(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvsub(&other.0))
  }

  pub fn mul(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvmul(&other.0))
  }

  pub fn div(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvudiv(&other.0))
  }

  pub fn rem(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvurem(&other.0))
  }

  pub fn bit_or(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvor(&other.0))
  }

  pub fn bit_and(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvand(&other.0))
  }

  pub fn bit_xor(&self, other: &Self) -> SymU128<'ctx> {
    SymU128(self.0.bvxor(&other.0))
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    SymU128(self.0.bvshl(&n_bits.0))
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    SymU128(self.0.bvlshr(&n_bits.0))
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvult(&other.0))
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvule(&other.0))
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvugt(&other.0))
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.bvuge(&other.0))
  }
}

impl<'ctx> SymBool<'ctx> {
  pub fn from(solver: &'ctx Solver, value: bool) -> Self {
    SymBool(Bool::from_bool(solver.ctx(), value))
  }

  pub fn from_ast(ast: Bool<'ctx>) -> Self {
    SymBool(ast)
  }

  pub fn new(solver: &'ctx Solver, prefix: &str) -> Self {
    SymBool(Bool::fresh_const(solver.ctx(), prefix))
  }

  pub fn as_inner(&self) -> &Bool<'ctx> {
    &self.0
  }

  pub fn collect(self) -> Dynamic<'ctx> {
    Dynamic::from_ast(&self.0)
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0._eq(&other.0))
  }

  pub fn not(&self) -> SymBool<'ctx> {
    SymBool(self.0.not())
  }

  pub fn and(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.and(&[&other.0]))
  }

  pub fn or(&self, other: &Self) -> SymBool<'ctx> {
    SymBool(self.0.or(&[&other.0]))
  }
}
