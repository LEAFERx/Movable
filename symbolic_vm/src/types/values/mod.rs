pub mod values_impl;
pub mod account_address;
pub mod primitives;
pub mod sort;

pub use values_impl::*;
pub use account_address::*;
pub use primitives::*;

use vm::errors::PartialVMResult;

use z3::{
  ast::Dynamic
};

pub trait SymbolicMoveValue<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>>;
}
