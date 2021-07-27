use move_core_types::{
  identifier::Identifier,
};

use vm::{
  errors::*,
  file_format::SignatureToken,
};

use crate::{
  plugin::{Plugin, PluginContext},
  runtime::{
    context::TypeContext,
    loader::{Loader, Function},
  },
  types::{
    memory::SymMemory,
    values::{SymBool, SymValue, SymbolicMoveValue, SymU64},
  },
};

use move_vm_types::loaded_data::runtime_types::Type;

use std::{
  collections::{HashMap, HashSet, VecDeque},
  convert::TryInto,
  default::Default,
  iter::FromIterator,
};

use z3::{
  ast::{Ast, Bool, Dynamic, exists_const},
  Context,
  Goal,
  Solver,
  SatResult,
  Tactic,
};
use z3_sys::AstKind;

#[derive(Default)]
pub struct FunctionSpec<'a> {
  requires: FunctionRequiresSpec<'a>,
  ensures: FunctionEnsuresSpec<'a>,
  aborts_if: FunctionAbortsIfSpec<'a>,
}

pub type FunctionRequiresCondition<'a> = dyn for<'ctx> Fn(
  &'ctx Context,
  &TypeContext<'ctx>,
  &[SymValue<'ctx>],        // Args
  &SymMemory<'ctx>,         // Old Memory
  &SymMemory<'ctx>,         // Memory
) -> SymBool<'ctx> + 'a;

pub struct FunctionRequiresSpec<'a> {
  condition: Box<FunctionRequiresCondition<'a>>,
}

pub type FunctionEnsuresCondition<'a> = dyn for<'ctx> Fn(
  &'ctx Context,
  &TypeContext<'ctx>,
  &[SymValue<'ctx>],        // Args
  &[SymValue<'ctx>],        // Return values
  &SymMemory<'ctx>,         // Old Memory
  &SymMemory<'ctx>,         // Memory
) -> SymBool<'ctx> + 'a;

pub struct FunctionEnsuresSpec<'a> {
  condition: Box<FunctionEnsuresCondition<'a>>,
}

pub type FunctionAbortsIfCondition<'a> = dyn for<'ctx> Fn(
  &'ctx Context,
  &TypeContext<'ctx>,
  &[SymValue<'ctx>],        // Args
  &SymMemory<'ctx>,         // Old Memory
  &SymMemory<'ctx>,         // Memory
) -> SymBool<'ctx> + 'a;

pub struct FunctionAbortsIfSpec<'a> {
  condition: Box<FunctionAbortsIfCondition<'a>>,
}

impl<'a> FunctionSpec<'a> {
  pub fn new(
    requires: FunctionRequiresSpec<'a>,
    ensures: FunctionEnsuresSpec<'a>,
    aborts_if: FunctionAbortsIfSpec<'a>,
  ) -> Self {
    Self {
      requires,
      ensures,
      aborts_if,
    }
  }

  pub fn requires<'ctx>(
    &self,
    z3_ctx: &'ctx Context,
    ty_ctx: &TypeContext<'ctx>,
    args: &[SymValue<'ctx>],
    old_memory: &SymMemory<'ctx>,
    memory: &SymMemory<'ctx>,
  ) -> SymBool<'ctx> {
    (self.requires.condition)(z3_ctx, ty_ctx, args, old_memory, memory)
  }

  pub fn ensures<'ctx>(
    &self,
    z3_ctx: &'ctx Context,
    ty_ctx: &TypeContext<'ctx>,
    args: &[SymValue<'ctx>],
    return_values: &[SymValue<'ctx>],
    old_memory: &SymMemory<'ctx>,
    memory: &SymMemory<'ctx>,
  ) -> SymBool<'ctx> {
    (self.ensures.condition)(z3_ctx, ty_ctx, args, return_values, old_memory, memory)
  }

  pub fn aborts_if<'ctx>(
    &self,
    z3_ctx: &'ctx Context,
    ty_ctx: &TypeContext<'ctx>,
    args: &[SymValue<'ctx>],
    old_memory: &SymMemory<'ctx>,
    memory: &SymMemory<'ctx>,
  ) -> SymBool<'ctx> {
    (self.aborts_if.condition)(z3_ctx, ty_ctx, args, old_memory, memory)
  }
}

impl<'a> FunctionRequiresSpec<'a> {
  pub fn new(f: impl for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a> FunctionEnsuresSpec<'a> {
  pub fn new(f: impl for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &[SymValue<'ctx>],        // Return values
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a> FunctionAbortsIfSpec<'a> {
  pub fn new(f: impl for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a, F> From<F> for FunctionRequiresSpec<'a>
where
  F: for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a
{
  fn from(f: F) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a, F> From<F> for FunctionEnsuresSpec<'a>
where
  F: for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &[SymValue<'ctx>],        // Return values
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a
{
  fn from(f: F) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a, F> From<F> for FunctionAbortsIfSpec<'a>
where
  F: for<'ctx> Fn(
    &'ctx Context,
    &TypeContext<'ctx>,
    &[SymValue<'ctx>],        // Args
    &SymMemory<'ctx>,         // Old Memory
    &SymMemory<'ctx>,         // Memory
  ) -> SymBool<'ctx> + 'a
{
  fn from(f: F) -> Self {
    Self { condition: Box::new(f) }
  }
}

impl<'a> Default for FunctionRequiresSpec<'a> {
  fn default() -> Self {
    Self {
      condition: Box::new(|z3_ctx: &Context, _ty_ctx: &TypeContext, _a: &[SymValue], _om: &SymMemory, _m: &SymMemory| SymBool::from(z3_ctx, true)),
    }
  }
}

impl<'a> Default for FunctionEnsuresSpec<'a> {
  fn default() -> Self {
    FunctionEnsuresSpec {
      condition: Box::new(|z3_ctx: &Context, _ty_ctx: &TypeContext, _a: &[SymValue], _r: &[SymValue], _om: &SymMemory, _m: &SymMemory| SymBool::from(z3_ctx, true)),
    }
  }
}

impl<'a> Default for FunctionAbortsIfSpec<'a> {
  fn default() -> Self {
    FunctionAbortsIfSpec {
      condition: Box::new(|z3_ctx: &Context, _ty_ctx: &TypeContext, _a: &[SymValue], _om: &SymMemory, _m: &SymMemory| SymBool::from(z3_ctx, false)),
    }
  }
}
