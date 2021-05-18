use move_core_types::vm_status::{StatusCode, VMStatus};
// use move_vm_types::{
//   gas_schedule::NativeCostIndex,
//   natives::function::native_gas,
// };
use std::{
  cell::RefCell,
  fmt::{self, Debug, Display},
  iter,
  rc::Rc,
};
use vm::{
  errors::*,
};

use z3::Context;

use crate::types::{
  values::{
    values_impl::{SymValue, SymValueImpl, SymContainerRef, SymIndexedRef, SymContainer, SymbolicContainerIndex},
  },
};

/// The locals for a function frame. It allows values to be read, written or taken
/// reference from.
#[derive(Debug)]
struct SymLocalsImpl<'ctx> {
  z3_ctx: &'ctx Context,
  locals: Vec<SymValueImpl<'ctx>>,
}

#[derive(Debug)]
pub struct SymLocals<'ctx>(Rc<RefCell<SymLocalsImpl<'ctx>>>);

impl<'ctx> SymLocalsImpl<'ctx> {
  fn new(z3_ctx: &'ctx Context, n: usize) -> Self {
    SymLocalsImpl {
      z3_ctx,
      locals: iter::repeat_with(|| SymValueImpl::Invalid)
        .take(n)
        .collect(),
    }
  }
}

impl<'ctx> SymLocals<'ctx> {
  pub fn new(z3_ctx: &'ctx Context, n: usize) -> Self {
    SymLocals(Rc::new(RefCell::new(SymLocalsImpl::new(z3_ctx, n))))
  }

  pub fn borrow_loc(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    // TODO: this is very similar to SharedContainer::borrow_elem. Find a way to
    // reuse that code?

    let v = &self.0.borrow().locals;

    if idx >= v.len() {
      return Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(
          format!(
            "index out of bounds when borrowing local: got: {}, len: {}",
            idx,
            v.len()
          )
        ),
      );
    }

    match &v[idx] {
      SymValueImpl::Container(c) => Ok(SymValue(SymValueImpl::ContainerRef(SymContainerRef::Local {
        container: c.copy_by_ref(),
        location: None,
      }))),

      SymValueImpl::U8(_)
      | SymValueImpl::U64(_)
      | SymValueImpl::U128(_)
      | SymValueImpl::Bool(_)
      | SymValueImpl::Address(_) => Ok(SymValue(SymValueImpl::IndexedRef(SymIndexedRef {
        container_ref: SymContainerRef::Local {
          container: Rc::clone(&self.0),
          location: None,
        },
        idx: SymbolicContainerIndex::Concrete(idx),
      }))),

      SymValueImpl::ContainerRef(_) | SymValueImpl::Invalid | SymValueImpl::IndexedRef(_) => Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot borrow local {:?}", &v[idx])),
      ),
    }
  }

  pub fn copy_loc(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    let r = self.0.borrow();
    let v = match &*r {
      SymContainer::Locals { locals: v, .. } => v,
      _ => unreachable!(),
    };

    match v.get(idx) {
      Some(SymValueImpl::Invalid) => Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot copy invalid value at index {}", idx)),
      ),
      Some(v) => Ok(SymValue(v.copy_value())),
      None => Err(
        PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(format!(
          "local index out of bounds: got {}, len: {}",
          idx,
          v.len()
        )),
      ),
    }
  }

  fn swap_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> PartialVMResult<SymValue<'ctx>> {
    let mut r = self.0.borrow_mut();
    let v = match &mut *r {
      SymContainer::Locals { locals: v, .. } => v,
      _ => unreachable!(),
    };

    match v.get_mut(idx) {
      Some(v) => {
        if let SymValueImpl::Container(r) = v {
          if Rc::strong_count(r) > 1 {
            return Err(
              PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                .with_message("moving container with dangling references".to_string()),
            );
          }
        }
        Ok(SymValue(std::mem::replace(v, x.0)))
      }
      None => Err(
        PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(format!(
          "local index out of bounds: got {}, len: {}",
          idx,
          v.len()
        )),
      ),
    }
  }

  pub fn move_loc(&mut self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    match self.swap_loc(idx, SymValue(SymValueImpl::Invalid))? {
      SymValue(SymValueImpl::Invalid) => Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot move invalid value at index {}", idx)),
      ),
      v => Ok(v),
    }
  }

  pub fn store_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> PartialVMResult<()> {
    self.swap_loc(idx, x)?;
    Ok(())
  }
}

impl<'ctx> Clone for SymLocalsImpl<'ctx> {
  fn clone(&self) -> Self {
    SymLocalsImpl {
      z3_ctx: self.z3_ctx.clone(),
      locals: Rc::new(RefCell::new(self.0.borrow().copy_value())),
    }
  }
}

impl<'ctx> Display for SymLocalsImpl<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    // TODO: this could panic.
    match &*self.0.borrow() {
      SymContainer::Locals { locals: v, .. } => write!(
        f,
        "{}",
        v.iter()
          .enumerate()
          .map(|(idx, val)| format!("[{}] {}", idx, val))
          .collect::<Vec<_>>()
          .join("\n")
      ),
      _ => unreachable!(),
    }
  }
}

