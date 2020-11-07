use vm::{
  errors::*,
};

use z3::{
  ast::{Ast, Bool, Dynamic, BV},
  Context,
};

use std::fmt;

use super::SymbolicMoveValue;

#[derive(Debug, Clone)]
pub struct SymU8<'ctx> {
  ast: BV<'ctx>,
  is_constant: bool,
}

#[derive(Debug, Clone)]
pub struct SymU64<'ctx> {
  ast: BV<'ctx>,
  is_constant: bool,
}

#[derive(Debug, Clone)]
pub struct SymU128<'ctx> {
  ast: BV<'ctx>,
  is_constant: bool,
}

#[derive(Debug, Clone)]
pub struct SymBool<'ctx> {
  ast: Bool<'ctx>,
  operand: Vec<Dynamic<'ctx>>,
}

// Consider to use a macro to do impl

impl<'ctx> SymU8<'ctx> {
  pub fn from(context: &'ctx Context, value: u8) -> Self {
    SymU8 {
      ast: BV::from_u64(context, value as u64, 8),
      is_constant: true,
    }
  }

  pub fn from_ast(ast: BV<'ctx>, is_constant: bool) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 8);
    SymU8 { ast, is_constant }
  }

  pub fn new(context: &'ctx Context, prefix: &str) -> Self {
    SymU8 {
      ast: BV::fresh_const(context, prefix, 8),
      is_constant: false,
    }
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.ast.zero_ext(64 - 8), self.is_constant)
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.ast.zero_ext(128 - 8), self.is_constant)
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    Ok(SymBool {
      ast: self.ast._eq(&other.ast),
      operand,
    })
  }

  pub fn add(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvadd(&other.ast),
      is_constant,
    }
  }

  pub fn sub(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvsub(&other.ast),
      is_constant,
    }
  }

  pub fn mul(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvmul(&other.ast),
      is_constant,
    }
  }

  pub fn div(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvudiv(&other.ast),
      is_constant,
    }
  }

  pub fn rem(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvurem(&other.ast),
      is_constant,
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvor(&other.ast),
      is_constant,
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvand(&other.ast),
      is_constant,
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU8<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU8 {
      ast: self.ast.bvxor(&other.ast),
      is_constant,
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU8 {
      ast: self.ast.bvshl(&n_bits.ast),
      is_constant,
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU8<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU8 {
      ast: self.ast.bvlshr(&n_bits.ast),
      is_constant,
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvult(&other.ast),
      operand,
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvule(&other.ast),
      operand,
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvugt(&other.ast),
      operand,
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvuge(&other.ast),
      operand,
    }
  }
}

impl<'ctx> SymU64<'ctx> {
  pub fn from(context: &'ctx Context, value: u64) -> Self {
    SymU64 {
      ast: BV::from_u64(context, value, 64),
      is_constant: true,
    }
  }

  pub fn from_ast(ast: BV<'ctx>, is_constant: bool) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 64);
    SymU64 { ast, is_constant }
  }

  pub fn new(context: &'ctx Context, prefix: &str) -> Self {
    SymU64 {
      ast: BV::fresh_const(context, prefix, 64),
      is_constant: false,
    }
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.ast.extract(7, 0), self.is_constant)
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    SymU128::from_ast(self.ast.zero_ext(128 - 64), self.is_constant)
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    Ok(SymBool {
      ast: self.ast._eq(&other.ast),
      operand,
    })
  }

  pub fn add(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvadd(&other.ast),
      is_constant,
    }
  }

  pub fn sub(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvsub(&other.ast),
      is_constant,
    }
  }

  pub fn mul(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvmul(&other.ast),
      is_constant,
    }
  }

  pub fn div(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvudiv(&other.ast),
      is_constant,
    }
  }

  pub fn rem(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvurem(&other.ast),
      is_constant,
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvor(&other.ast),
      is_constant,
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvand(&other.ast),
      is_constant,
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU64<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU64 {
      ast: self.ast.bvxor(&other.ast),
      is_constant,
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU64 {
      ast: self.ast.bvshl(&n_bits.ast),
      is_constant,
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU64<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU64 {
      ast: self.ast.bvlshr(&n_bits.ast),
      is_constant,
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvult(&other.ast),
      operand,
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvule(&other.ast),
      operand,
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvugt(&other.ast),
      operand,
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvuge(&other.ast),
      operand,
    }
  }
}

impl<'ctx> SymU128<'ctx> {
  pub fn from(context: &'ctx Context, value: u128) -> Self {
    let ctx = context;
    let ast =
      BV::from_u64(ctx, (value >> 64) as u64, 64).concat(&BV::from_u64(ctx, value as u64, 64));
    SymU128 {
      ast,
      is_constant: true,
    }
  }

  pub fn from_ast(ast: BV<'ctx>, is_constant: bool) -> Self {
    // Maybe return a result instead?
    assert!(ast.get_size() == 128);
    SymU128 { ast, is_constant }
  }

  pub fn new(context: &'ctx Context, prefix: &str) -> Self {
    SymU128 {
      ast: BV::fresh_const(context, prefix, 128),
      is_constant: false,
    }
  }

  pub fn cast_u8(self) -> SymU8<'ctx> {
    SymU8::from_ast(self.ast.extract(7, 0), self.is_constant)
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    SymU64::from_ast(self.ast.extract(63, 0), self.is_constant)
  }

  pub fn as_inner(&self) -> &BV<'ctx> {
    &self.ast
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    Ok(SymBool {
      ast: self.ast._eq(&other.ast),
      operand,
    })
  }

  pub fn add(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvadd(&other.ast),
      is_constant,
    }
  }

  pub fn sub(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvsub(&other.ast),
      is_constant,
    }
  }

  pub fn mul(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvmul(&other.ast),
      is_constant,
    }
  }

  pub fn div(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvudiv(&other.ast),
      is_constant,
    }
  }

  pub fn rem(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvurem(&other.ast),
      is_constant,
    }
  }

  pub fn bit_or(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvor(&other.ast),
      is_constant,
    }
  }

  pub fn bit_and(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvand(&other.ast),
      is_constant,
    }
  }

  pub fn bit_xor(&self, other: &Self) -> SymU128<'ctx> {
    let is_constant = self.is_constant && other.is_constant;
    SymU128 {
      ast: self.ast.bvxor(&other.ast),
      is_constant,
    }
  }

  pub fn shl(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU128 {
      ast: self.ast.bvshl(&n_bits.ast),
      is_constant,
    }
  }

  pub fn shr(&self, n_bits: &SymU8<'ctx>) -> SymU128<'ctx> {
    let is_constant = self.is_constant && n_bits.is_constant;
    SymU128 {
      ast: self.ast.bvlshr(&n_bits.ast),
      is_constant,
    }
  }

  pub fn lt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvult(&other.ast),
      operand,
    }
  }

  pub fn le(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvule(&other.ast),
      operand,
    }
  }

  pub fn gt(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvugt(&other.ast),
      operand,
    }
  }

  pub fn ge(&self, other: &Self) -> SymBool<'ctx> {
    let mut operand = vec![];
    if !self.is_constant {
      operand.push(Dynamic::from_ast(&self.ast));
    }
    if !other.is_constant {
      operand.push(Dynamic::from_ast(&other.ast));
    }
    SymBool {
      ast: self.ast.bvuge(&other.ast),
      operand,
    }
  }
}

impl<'ctx> SymBool<'ctx> {
  pub fn from(context: &'ctx Context, value: bool) -> Self {
    SymBool {
      ast: Bool::from_bool(context, value),
      operand: vec![],
    }
  }

  pub fn from_ast(ast: Bool<'ctx>, operand: Vec<Dynamic<'ctx>>) -> Self {
    SymBool {
      ast,
      operand, //? Should be right. Revise it.
    }
  }

  pub fn new(context: &'ctx Context, prefix: &str) -> Self {
    SymBool {
      ast: Bool::fresh_const(context, prefix),
      operand: vec![],
    }
  }

  pub fn as_inner(&self) -> &Bool<'ctx> {
    &self.ast
  }

  pub(crate) fn set_ast(&mut self, ast: Bool<'ctx>) {
    self.ast = ast; // !!! bad figure it out
  }

  pub fn operand(&self) -> Vec<Dynamic<'ctx>> {
    self.operand.clone()
  }

  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    Ok(SymBool {
      ast: self.ast._eq(&other.ast),
      operand: vec![Dynamic::from_ast(&self.ast), Dynamic::from_ast(&other.ast)],
    })
  }

  pub fn not(&self) -> SymBool<'ctx> {
    SymBool {
      ast: self.ast.not(),
      operand: vec![Dynamic::from_ast(&self.ast)],
    }
  }

  pub fn and(context: &'ctx Context, operands: &[SymBool<'ctx>], construct_operand: bool) -> SymBool<'ctx> {
    if construct_operand {
      SymBool {
        ast: Bool::and(context, &operands.iter().map(|v| &v.ast).collect::<Vec<_>>()),
        operand: operands.iter().map(|v| Dynamic::from_ast(&v.ast)).collect(),
      }
    } else {
      SymBool {
        ast: Bool::and(context, &operands.iter().map(|v| &v.ast).collect::<Vec<_>>()),
        operand: vec![],
      }
    }
  }

  pub fn or(context: &'ctx Context, operands: &[SymBool<'ctx>], construct_operand: bool) -> SymBool<'ctx> {
    if construct_operand {
      SymBool {
        ast: Bool::or(context, &operands.iter().map(|v| &v.ast).collect::<Vec<_>>()),
        operand: operands.iter().map(|v| Dynamic::from_ast(&v.ast)).collect(),
      }
    } else {
      SymBool {
        ast: Bool::or(context, &operands.iter().map(|v| &v.ast).collect::<Vec<_>>()),
        operand: vec![],
      }
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU8<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU64<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymU128<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.ast))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymBool<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
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