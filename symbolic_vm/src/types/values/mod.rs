pub mod values_impl;
pub mod account_address;
pub mod primitives;
pub mod types;

pub use values_impl::*;
pub use account_address::*;
pub use primitives::*;

use move_core_types::language_storage::TypeTag;
use vm::errors::PartialVMResult;
use crate::runtime::context::TypeContext;

use z3::{
  ast::Dynamic
};

pub trait SymbolicMoveValue<'ctx> {
  fn as_runtime_ast(&self, ty_ctx: &TypeContext<'ctx>) -> PartialVMResult<Dynamic<'ctx>>;

  fn as_value_ast(&self, ty_ctx: &TypeContext<'ctx>, ty: &TypeTag) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(ty_ctx.runtime_ast_to_value_ast(self.as_runtime_ast(ty_ctx)?, ty))
  }
}
