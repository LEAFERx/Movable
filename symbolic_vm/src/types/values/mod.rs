pub mod values_impl;
pub mod account_address;
pub mod locals;
pub mod primitives;
pub mod sort;
pub mod struct_impl;
pub mod vector;

pub use values_impl::*;
pub use account_address::*;
pub use primitives::*;
pub use locals::*;

use vm::errors::PartialVMResult;

use z3::{
  ast::Dynamic
};

pub trait SymbolicMoveValue<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>>;
}
