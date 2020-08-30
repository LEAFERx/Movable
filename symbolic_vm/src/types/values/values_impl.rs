use libra_types::{
  account_address::AccountAddress,
  vm_error::{
    StatusCode,
    VMStatus,
  },
};
use move_core_types::gas_schedule::{
  words_in, AbstractMemorySize, GasAlgebra, GasCarrier, CONST_SIZE, REFERENCE_SIZE, STRUCT_SIZE,
};
use move_vm_types::{
  // gas_schedule::NativeCostIndex,
  loaded_data::types::{FatStructType, FatType},
  // natives::function::native_gas,
  values::{Struct, VMValueCast, Value},
};
use std::{
  cell::{Ref, RefCell, RefMut},
  fmt::{self, Debug, Display},
  ops::Add,
  rc::Rc,
};
use vm::{
  errors::*,
  file_format::{Constant, SignatureToken},
};

use z3::{
  ast::Dynamic,
  Context,
};

use crate::types::{
  values::{
    account_address::SymAccountAddress,
    primitives::{SymBool, SymU128, SymU64, SymU8},
    struct_impl::SymStructImpl,
    vector::SymVectorImpl,
    SymbolicMoveValue,
  },
};

/***************************************************************************************
*
* Internal Types
*
*   Internal representation of the Move value calculus. These types are abstractions
*   over the concrete Move concepts and may carry additonal information that is not
*   defined by the language, but required by the implementation.
*
**************************************************************************************/

/// Runtime representation of a Move value.
#[derive(Debug)]
pub(super) enum SymValueImpl<'ctx> {
  Invalid,

  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
  Bool(SymBool<'ctx>),
  Address(SymAccountAddress<'ctx>),
  Signer(SymAccountAddress<'ctx>),

  Container(Rc<RefCell<SymContainer<'ctx>>>),

  ContainerRef(SymContainerRef<'ctx>),
  IndexedRef(SymIndexedRef<'ctx>),
}

/// A container is a collection of values. It is used to represent data structures like a
/// Move vector or struct.
///
/// There is one general container that can be used to store an array of any values, same
/// type or not, and a few specialized flavors to offer compact memory layout for small
/// primitive types.
///
/// Except when not owned by the VM stack, a container always lives inside an Rc<RefCell<>>,
/// making it possible to be shared by references.
// #[derive(Debug)]
// pub(super) enum SymContainerImpl<'ctx> {
//   General(Vec<SymValueImpl<'ctx>>),
//   U8(Vec<SymU8<'ctx>>),
//   U64(Vec<SymU64<'ctx>>),
//   U128(Vec<SymU128<'ctx>>),
//   Bool(Vec<SymBool<'ctx>>),
// }

#[derive(Debug)]
pub(super) enum SymContainer<'ctx> {
  Locals {
    context: &'ctx Context,
    locals: Vec<SymValueImpl<'ctx>>,
  },
  Struct(SymStructImpl<'ctx>),
  Vector(SymVectorImpl<'ctx>),
  VecU8(SymVectorImpl<'ctx>),
  VecU64(SymVectorImpl<'ctx>),
  VecU128(SymVectorImpl<'ctx>),
  VecBool(SymVectorImpl<'ctx>),
}

/// A ContainerRef is a direct reference to a container, which could live either in the frame
/// or in global storage. In the latter case, it also keeps a status flag indicating whether
/// the container has been possibly modified.
/// The location is used for Struct and Vector
#[derive(Debug)]
pub(super) enum SymContainerRef<'ctx> {
  Local {
    container: Rc<RefCell<SymContainer<'ctx>>>,
    location: Option<Box<SymIndexedRef<'ctx>>>,
  },
  Global {
    status: Rc<RefCell<GlobalDataStatus>>,
    container: Rc<RefCell<SymContainer<'ctx>>>,
    location: Option<Box<SymIndexedRef<'ctx>>>,
  },
}

/// Status for global (on-chain) data:
/// Clean - the data was only read.
/// Dirty - the data was possibly modified.
#[derive(Debug, Clone, Copy)]
pub(super) enum GlobalDataStatus {
  Clean,
  Dirty,
}

// Symbolic is used on vector, while Concrete is used on locals and struct
// According to Move design, we won't use Concrete on vector, but currently
// Movable supports it.
// TODO: evaluate this.
#[derive(Debug)]
pub(super) enum SymbolicContainerIndex<'ctx> {
  Concrete(usize),
  Symbolic(SymU64<'ctx>),
}

/// A Move reference pointing to an element in a container.
#[derive(Debug)]
pub(super) struct SymIndexedRef<'ctx> {
  pub(super) idx: SymbolicContainerIndex<'ctx>,
  pub(super) container_ref: SymContainerRef<'ctx>,
}

/// An umbrella enum for references. It is used to hide the internals of the public type
/// Reference.
#[derive(Debug)]
enum SymReferenceImpl<'ctx> {
  IndexedRef(SymIndexedRef<'ctx>),
  ContainerRef(SymContainerRef<'ctx>),
}

/***************************************************************************************
*
* Public Types
*
*   Types visible from outside the module. They are almost exclusively wrappers around
*   the internal representation, acting as public interfaces. The methods they provide
*   closely resemble the Move concepts their names suggest: move_local, borrow_field,
*   pack, unpack, etc.
*
*   They are opaque to an external caller by design -- no knowledge about the internal
*   representation is given and they can only be manipulated via the public methods,
*   which is to ensure no arbitratry invalid states can be created unless some crucial
*   internal invariants are violated.
*
**************************************************************************************/

/// A reference to a Move struct that allows you to take a reference to one of its fields.
#[derive(Debug)]
pub struct SymStructRef<'ctx>(SymContainerRef<'ctx>);

/// A generic Move reference that offers two functinalities: read_ref & write_ref.
#[derive(Debug)]
pub struct SymReference<'ctx>(SymReferenceImpl<'ctx>);

/// A Move value -- a wrapper around `SymValueImpl<'ctx>` which can be created only through valid
/// means.
#[derive(Debug)]
pub struct SymValue<'ctx>(pub(super) SymValueImpl<'ctx>);

/// An integer value in Move.
#[derive(Debug)]
pub enum SymIntegerValue<'ctx> {
  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
}

/// A Move struct.
#[derive(Debug)]
pub struct SymStruct<'ctx>(SymContainer<'ctx>);

/// A special value that lives in global storage.
///
/// Callers are allowed to take global references from a `GlobalValue`. A global value also contains
/// an internal flag, indicating whether the value has potentially been modified or not.
///
/// For any given value in storage, only one `GlobalValue` may exist to represent it at any time.
/// This means that:
/// * `GlobalValue` **does not** and **cannot** implement `Clone`!
/// * a borrowed reference through `borrow_global` is represented through a `&GlobalValue`.
/// * `borrow_global_mut` is also represented through a `&GlobalValue` -- the bytecode verifier
///   enforces mutability restrictions.
/// * `move_from` is represented through an owned `GlobalValue`.
#[derive(Debug)]
pub struct SymGlobalValue<'ctx> {
  status: Rc<RefCell<GlobalDataStatus>>,
  container: Rc<RefCell<SymContainer<'ctx>>>,
}

/***************************************************************************************
*
* Misc
*
*   Miscellaneous helper functions.
*
**************************************************************************************/
impl<'ctx> SymContainer<'ctx> {
  pub(super) fn len(&self) -> usize {
    use SymContainer::*;

    match self {
      // !!! figure it out
      Locals { locals, .. } => locals.len(),
      Struct(v) => v.len(),
      Vector(_v) => 0, // v.len(),
      VecU8(_v) => 0, // v.len(),
      VecU64(_v) => 0, // v.len(),
      VecU128(_v) => 0, // v.len(),
      VecBool(_v) => 0, // v.len(),
    }
  }
}

impl<'ctx> SymValueImpl<'ctx> {
  pub(super) fn new_container(container: SymContainer<'ctx>) -> Self {
    Self::Container(Rc::new(RefCell::new(container)))
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn is_valid_script_arg(&self, sig: &SignatureToken) -> bool {
    match (sig, &self.0) {
      (SignatureToken::U8, SymValueImpl::U8(_)) => true,
      (SignatureToken::U64, SymValueImpl::U64(_)) => true,
      (SignatureToken::U128, SymValueImpl::U128(_)) => true,
      (SignatureToken::Bool, SymValueImpl::Bool(_)) => true,
      (SignatureToken::Address, SymValueImpl::Address(_)) => true,
      (SignatureToken::Vector(ty), SymValueImpl::Container(r)) => {
        match (&**ty, &*r.borrow()) {
          (SignatureToken::U8, SymContainer::VecU8(_)) => true,
          _ => false,
        }
      }
      _ => false,
    }
  }
}

impl<'ctx> SymbolicContainerIndex<'ctx> {
  pub(super) fn to_concrete(&self) -> Option<usize> {
    use SymbolicContainerIndex::*;

    match self {
      Concrete(idx) => Some(*idx),
      Symbolic(_) => None,
    }
  }
}

macro_rules! get_local_by_idx {
  ($locals: ident, $idx: expr) => {
    {
      let idx = $idx.to_concrete().ok_or(
        VMStatus::new(StatusCode::INVALID_DATA)
          .with_message(format!("Symbolic index {:?} cannot be used on Locals", $idx))
      )?;
      &$locals[idx]
    }
  };
}

macro_rules! set_local_by_idx {
  ($locals: ident, $idx: expr, $val: expr) => {
    {
      let idx = $idx.to_concrete().ok_or(
        VMStatus::new(StatusCode::INVALID_DATA)
          .with_message(format!("Symbolic index {:?} cannot be used on Locals", $idx))
      )?;
      $locals[idx] = $val;
    }
  };
}

/***************************************************************************************
*
* Borrows (Internal)
*
*   Helper functions to handle Rust borrows. When borrowing from a RefCell, we want
*   to return an error instead of panicking.
*
**************************************************************************************/

fn take_unique_ownership<T: Debug>(r: Rc<RefCell<T>>) -> VMResult<T> {
  match Rc::try_unwrap(r) {
    Ok(cell) => Ok(cell.into_inner()),
    Err(r) => Err(
      VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
        .with_message(format!("moving value {:?} with dangling references", r)),
    ),
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  pub(super) fn borrow(&self) -> Ref<SymContainer<'ctx>> {
    match self {
      Self::Local { container, .. } | Self::Global { container, .. } => container.borrow(),
    }
  }

  pub(super) fn borrow_mut(&self) -> RefMut<SymContainer<'ctx>> {
    match self {
      Self::Local { container, .. } => container.borrow_mut(),
      Self::Global { container, status, .. } => {
        *status.borrow_mut() = GlobalDataStatus::Dirty;
        container.borrow_mut()
      }
    }
  }
}

/***************************************************************************************
*
* Reference Conversions (Internal)
*
*   Helpers to obtain a Rust reference to a value via a VM reference. Required for
*   equalities.
*
**************************************************************************************/
trait VMValueRef<T> {
  fn value_ref(&self) -> VMResult<&T>;
}

macro_rules! impl_vm_value_ref {
  ($ty: ty, $tc: ident) => {
    impl<'ctx> VMValueRef<$ty> for SymValueImpl<'ctx> {
      fn value_ref(&self) -> VMResult<&$ty> {
        match self {
          SymValueImpl::$tc(x) => Ok(x),
          _ => Err(
            VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
              "cannot take {:?} as &{}",
              self,
              stringify!($ty)
            )),
          ),
        }
      }
    }
  };
}

impl_vm_value_ref!(SymU8<'ctx>, U8);
impl_vm_value_ref!(SymU64<'ctx>, U64);
impl_vm_value_ref!(SymU128<'ctx>, U128);
impl_vm_value_ref!(SymBool<'ctx>, Bool);
impl_vm_value_ref!(SymAccountAddress<'ctx>, Address);

// impl<'ctx> SymValueImpl<'ctx> {
//   fn as_value_ref<T>(&self) -> VMResult<&T>
//   where
//     Self: VMValueRef<T>,
//   {
//     VMValueRef::value_ref(self)
//   }
// }

/***************************************************************************************
*
* Copy Value
*
*   Implementation of Move copy. Extra care needs to be taken when copying references.
*   It is intentional we avoid implementing the standard library trait Clone, to prevent
*   surprising behaviors from happening.
*
**************************************************************************************/
impl<'ctx> SymValueImpl<'ctx> {
  pub(super) fn copy_value(&self) -> Self {
    use SymValueImpl::*;

    match self {
      Invalid => Invalid,

      U8(x) => U8(x.clone()),
      U64(x) => U64(x.clone()),
      U128(x) => U128(x.clone()),
      Bool(x) => Bool(x.clone()),
      Address(x) => Address(x.clone()),
      // TODO copying resource?
      Signer(x) => Signer(x.clone()),

      ContainerRef(r) => ContainerRef(r.copy_value()),
      IndexedRef(r) => IndexedRef(r.copy_value()),

      // When cloning a container, we need to make sure we make a deep
      // copy of the data instead of a shallow copy of the Rc.
      Container(c) => Container(Rc::new(RefCell::new(c.borrow().copy_value()))),
    }
  }
}

impl<'ctx> SymContainer<'ctx> {
  pub(super) fn copy_value(&self) -> Self {
    use SymContainer::*;

    match self {
      Locals { context, locals } => Locals {
        context,
        locals: locals.iter().map(|x| x.copy_value()).collect(),
      },
      Struct(v) => Struct(v.copy_value()),
      Vector(v)
      | VecU8(v)
      | VecU64(v)
      | VecU128(v)
      | VecBool(v) => Vector(v.copy_value()),
    }
  }
}

impl<'ctx> SymbolicContainerIndex<'ctx> {
  fn copy_value(&self) -> Self {
    use SymbolicContainerIndex::*;
  
    match self {
      Concrete(idx) => Concrete(*idx),
      Symbolic(idx) => Symbolic(idx.clone()),
    }
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn copy_value(&self) -> Self {
    Self {
      idx: self.idx.copy_value(),
      container_ref: self.container_ref.copy_value(),
    }
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn copy_value(&self) -> Self {
    match self {
      Self::Local { container, location } => Self::Local {
        container: Rc::clone(container),
        location: match location {
          Some(loc) => Some(Box::new(loc.copy_value())),
          None => None,
        },
      },
      Self::Global { status, container, location } => Self::Global {
        status: Rc::clone(status),
        container: Rc::clone(container),
        location: match location {
          Some(loc) => Some(Box::new(loc.copy_value())),
          None => None,
        },
      },
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn copy_value(&self) -> Self {
    Self(self.0.copy_value())
  }
}

/***************************************************************************************
*
* Equality
*
*   Equality tests of Move values. Errors are raised when types mismatch.
*
*   It is intented to NOT use or even implement the standard library traits Eq and
*   Partial Eq due to:
*     1. They do not allow errors to be returned.
*     2. They can be invoked without the user being noticed thanks to operator
*        overloading.
*
*   Eq and Partial Eq must also NOT be derived for the reasons above plus that the
*   derived implementation differs from the semantics we want.
*
**************************************************************************************/

impl<'ctx> SymValueImpl<'ctx> {
  fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    use SymValueImpl::*;

    let res = match (self, other) {
      (U8(l), U8(r)) => l.equals(r)?,
      (U64(l), U64(r)) => l.equals(r)?,
      (U128(l), U128(r)) => l.equals(r)?,
      (Bool(l), Bool(r)) => l.equals(r)?,
      (Address(l), Address(r)) => l.equals(r)?,
      (Signer(l), Signer(r)) => l.equals(r)?,

      (Container(l), Container(r)) => l.borrow().equals(&*r.borrow())?,

      (ContainerRef(l), ContainerRef(r)) => l.equals(r)?,
      (IndexedRef(l), IndexedRef(r)) => l.equals(r)?,

      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot compare values: {:?}, {:?}", self, other)),
        )
      }
    };

    Ok(res)
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    use SymContainer::*;

    let res = match (&self, &other) {
      // Let's just assume context is equal for same <'ctx>
      (Locals { context, locals: l }, Locals { locals: r, .. }) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(context, false));
        }
        let mut res = SymBool::from(context, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
      (Struct(l), Struct(r)) => SymBool::from_ast(l.equals(r)),
      (Vector(l), Vector(r)) 
      | (VecU8(l), VecU8(r))
      | (VecU64(l), VecU64(r))
      | (VecU128(l), VecU128(r))
      | (VecBool(l), VecBool(r))
      => SymBool::from_ast(l.equals(r)),
      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot compare container values: {:?}, {:?}",
            self, other
          )),
        )
      }
    };

    Ok(res)
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    self.borrow().equals(&*other.borrow())
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  // This function may not implement exact the same semantics of `equals` as the `SymContainer` is using
  // data structure like current(2020.08.24) Move but symplified. However, it should be ok in most cases.
  fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    use SymContainer::*;

    macro_rules! eq {
      ($v1: expr) => {
        match &*other.container_ref.borrow() {
          Locals { locals: v2, ..} => $v1.equals(get_local_by_idx!(v2, other.idx)),
          Struct(v2) => $v1.equals(&v2.get(&other.idx)?.0),
          Vector(v2)
          | VecU8(v2)
          | VecU64(v2)
          | VecU128(v2)
          | VecBool(v2) => $v1.equals(&v2.get(&other.idx)?.0),
        }
      };
    }

    match &*self.container_ref.borrow() {
      Locals { locals: v1, ..} => {
        let idx = self.idx.to_concrete().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("Symbolic index {:?} cannot be used on Locals", self.idx))
        )?;
        eq!(v1[idx])
      },
      Struct(v) => eq!(v.get(&other.idx)?.0),
      Vector(v)
      | VecU8(v)
      | VecU64(v)
      | VecU128(v)
      | VecBool(v) => eq!(v.get(&self.idx)?.0),
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    self.0.equals(&other.0)
  }
}

/***************************************************************************************
*
* Read Ref
*
*   Implementation of the Move operation read ref.
*
**************************************************************************************/

impl<'ctx> SymContainerRef<'ctx> {
  fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    Ok(SymValue(SymValueImpl::new_container(
      self.borrow().copy_value(),
    )))
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    use SymContainer::*;

    let res = match &*self.container_ref.borrow() {
      Locals { locals: v, ..} => SymValue(get_local_by_idx!(v, self.idx).copy_value()),
      Struct(v) => v.get(&self.idx)?,
      Vector(v)
      | VecU8(v)
      | VecU64(v)
      | VecU128(v)
      | VecBool(v) => v.get(&self.idx)?,
    };

    Ok(res)
  }
}

impl<'ctx> SymReferenceImpl<'ctx> {
  fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    match self {
      Self::ContainerRef(r) => r.read_ref(),
      Self::IndexedRef(r) => r.read_ref(),
    }
  }
}

impl<'ctx> SymStructRef<'ctx> {
  pub fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    self.0.read_ref()
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    self.0.read_ref()
  }
}

/***************************************************************************************
*
* Write Ref
*
*   Implementation of the Move operation write ref.
*
**************************************************************************************/

impl<'ctx> SymContainerRef<'ctx> {
  fn write_propagate(&self) -> VMResult<()> {
    let loc = match self {
      Self::Local { location, .. } => location,
      Self::Global { location, .. } => location,
    };
    match loc {
      // copy_value here because read_ref and write_ref will consume self
      Some(r) => r.copy_value().write_ref(self.copy_value().read_ref()?)?,
      None => {},
    }
    Ok(())
  }

  fn write_ref(self, v: SymValue<'ctx>) -> VMResult<()> {
    match v.0 {
      SymValueImpl::Container(r) => {
        *self.borrow_mut() = take_unique_ownership(r)?;
        // TODO: can we simply take the Rc?
        self.write_propagate()?;
      }
      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to container ref {:?}",
            v, self
          )),
        )
      }
    }
    Ok(())
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn write_ref(self, x: SymValue<'ctx>) -> VMResult<()> {
    match &x.0 {
      SymValueImpl::IndexedRef(_)
      | SymValueImpl::ContainerRef(_)
      | SymValueImpl::Invalid => {
      // TODO: comment this out for write_propagte
      // find a better way?
      // | SymValueImpl::Container(_) => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
      _ => (),
    }

    match (&mut *self.container_ref.borrow_mut(), &x.0) {
      (SymContainer::Locals { locals: v, .. }, _) => set_local_by_idx!(v, self.idx, x.0),
      (SymContainer::Struct(v), _) => v.set(&self.idx, x)?,
      (SymContainer::Vector(v), _)
      | (SymContainer::VecU8(v), SymValueImpl::U8(_))
      | (SymContainer::VecU64(v), SymValueImpl::U64(_))
      | (SymContainer::VecU128(v), SymValueImpl::U128(_))
      | (SymContainer::VecBool(v), SymValueImpl::Bool(_)) => v.set(&self.idx, x)?,
      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
    }
    self.container_ref.write_propagate()?;
    Ok(())
  }
}

impl<'ctx> SymReferenceImpl<'ctx> {
  fn write_ref(self, x: SymValue<'ctx>) -> VMResult<()> {
    match self {
      Self::ContainerRef(r) => r.write_ref(x),
      Self::IndexedRef(r) => r.write_ref(x),
    }
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn write_ref(self, x: SymValue<'ctx>) -> VMResult<()> {
    self.0.write_ref(x)
  }
}

/***************************************************************************************
*
* Borrows (Move)
*
*   Implementation of borrowing in Move: borrow field, borrow local and infrastructure
*   to support borrowing an element from a vector.
*
**************************************************************************************/

impl<'ctx> SymContainerRef<'ctx> {
  pub(super) fn borrow_elem(&self, idx: SymbolicContainerIndex<'ctx>) -> VMResult<SymValueImpl<'ctx>> {
    use SymbolicContainerIndex::*;

    let r = self.borrow();

    match &idx {
      Concrete(idx) => if *idx >= r.len() {
        return Err(
          VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
            "index out of bounds when borrowing container element: got: {}, len: {}",
            idx,
            r.len()
          )),
        );
      },
      // Symbolic is only used on vector, check in vector::native_borrow
      Symbolic(_) => {},
    }

    // TODO: Currently except locals all ref is in indexed ref, it seems ok to me but nee further consideration.
    let res = match &*r {
      SymContainer::Locals { locals: v, .. } => match get_local_by_idx!(v, idx) {
        // TODO: check for the impossible combinations.
        SymValueImpl::Container(container) => {
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: Rc::clone(container),
              // Locals does not need location
              location: None,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: Rc::clone(container),
              // Locals does not need location
              location: None
            },
          };
          SymValueImpl::ContainerRef(r)
        }
        _ => SymValueImpl::IndexedRef(SymIndexedRef {
          idx,
          container_ref: self.copy_value(),
        }),
      },
      SymContainer::Struct(v) => match &v.get(&idx)?.0 {
        SymValueImpl::Container(container) => {
          let location = Some(Box::new(SymIndexedRef {
            idx,
            container_ref: self.copy_value(),
          }));
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: Rc::clone(container),
              location,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: Rc::clone(container),
              location,
            }
          };
          SymValueImpl::ContainerRef(r)
        },
        _ => SymValueImpl::IndexedRef(SymIndexedRef {
          idx,
          container_ref: self.copy_value(),
        }),
      },
      SymContainer::Vector(v) => match &v.get(&idx)?.0 {
        SymValueImpl::Container(container) => {
          let location = Some(Box::new(SymIndexedRef {
            idx,
            container_ref: self.copy_value(),
          }));
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: Rc::clone(container),
              location,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: Rc::clone(container),
              location,
            }
          };
          SymValueImpl::ContainerRef(r)
        },
        _ => SymValueImpl::IndexedRef(SymIndexedRef {
          idx,
          container_ref: self.copy_value(),
        }),
      },
      _ => SymValueImpl::IndexedRef(SymIndexedRef {
        idx,
        container_ref: self.copy_value(),
      }),
    };

    Ok(res)
  }
}

impl<'ctx> SymStructRef<'ctx> {
  pub fn borrow_field(&self, idx: usize) -> VMResult<SymValue<'ctx>> {
    Ok(SymValue(self.0.borrow_elem(SymbolicContainerIndex::Concrete(idx))?))
  }
}

/***************************************************************************************
*
* Public Value Constructors
*
*   Constructors to allow values to be created outside this module.
*
**************************************************************************************/
impl<'ctx> SymValue<'ctx> {
  pub fn from_deserialized_value(
    context: &'ctx Context,
    value: Value,
    ty: &FatType,
  ) -> VMResult<Self> {
    match ty {
      FatType::Bool => Ok(SymValue::from_bool(context, value.value_as()?)),
      FatType::U8 => Ok(SymValue::from_u8(context, value.value_as()?)),
      FatType::U64 => Ok(SymValue::from_u64(context, value.value_as()?)),
      FatType::U128 => Ok(SymValue::from_u128(context, value.value_as()?)),
      FatType::Address => Ok(SymValue::from_address(context, value.value_as()?)),
      FatType::Signer => Ok(SymValue::from_signer(context, value.value_as()?)),
      FatType::Vector(_) => unimplemented!(),
      FatType::Struct(struct_type) => Ok(SymValue::from_deserialized_struct(
        context,
        VMValueCast::cast(value)?,
        struct_type,
      )?),
      FatType::Reference(_) | FatType::MutableReference(_) | FatType::TyParam(_) => Err(
        VMStatus::new(StatusCode::INVALID_DATA).with_message(format!(
          "Such type {:?} is not possibly from deserialzed!",
          ty
        )),
      ),
    }
  }

  pub fn from_ast_with_type_info(
    context: &'ctx Context,
    ast: Dynamic<'ctx>,
    ty: &FatType
  ) -> VMResult<Self> {
    match ty {
      FatType::Bool => {
        let ast = ast.as_bool().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        Ok(SymValue::from_sym_bool(SymBool::from_ast(ast)))
      }
      FatType::U8 => {
        let ast = ast.as_bv().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        Ok(SymValue::from_sym_u8(SymU8::from_ast(ast)))
      }
      FatType::U64 => {
        let ast = ast.as_bv().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        Ok(SymValue::from_sym_u64(SymU64::from_ast(ast)))
      }
      FatType::U128 => {
        let ast = ast.as_bv().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        Ok(SymValue::from_sym_u128(SymU128::from_ast(ast)))
      }
      FatType::Address | FatType::Signer => {
        let ast = ast.as_bv().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        let addr = SymAccountAddress::from_ast(ast);
        Ok(SymValue::from_sym_address(addr))
      }
      FatType::Vector(ty) => {
        let ast = ast.as_datatype().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        let res = match ty.as_ref() {
          ty @ FatType::U8 => SymValue::from_sym_vec_u8(SymVectorImpl::from_ast(context, ty, ast)?),
          ty @ FatType::U64 => SymValue::from_sym_vec_u64(SymVectorImpl::from_ast(context, ty, ast)?),
          ty @ FatType::U128 => SymValue::from_sym_vec_u128(SymVectorImpl::from_ast(context, ty, ast)?),
          ty @ FatType::Bool => SymValue::from_sym_vec_bool(SymVectorImpl::from_ast(context, ty, ast)?),
          ty @ _ => SymValue::from_sym_vector(SymVectorImpl::from_ast(context, ty, ast)?),
        };
        Ok(res)
      },
      FatType::Struct(ty) => {
        let ast = ast.as_datatype().ok_or(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        let s = SymStructImpl::from_ast(context, ty.as_ref(), ast)?;
        Ok(SymValue(SymValueImpl::new_container(SymContainer::Struct(s))))
      },
      FatType::Reference(_) | FatType::MutableReference(_) | FatType::TyParam(_) => {
        Err(
          VMStatus::new(StatusCode::INVALID_DATA)
            .with_message(format!("{:?} is invalid when calling SymValue::from_ast_with_type_info", ty))
        )
      }
    }
  }

  pub fn from_u8(context: &'ctx Context, value: u8) -> Self {
    SymValue(SymValueImpl::U8(SymU8::from(context, value)))
  }

  pub fn from_sym_u8(sym: SymU8<'ctx>) -> Self {
    SymValue(SymValueImpl::U8(sym))
  }

  pub fn new_u8(context: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U8(SymU8::new(context, prefix)))
  }

  pub fn from_u64(context: &'ctx Context, value: u64) -> Self {
    SymValue(SymValueImpl::U64(SymU64::from(context, value)))
  }

  pub fn from_sym_u64(sym: SymU64<'ctx>) -> Self {
    SymValue(SymValueImpl::U64(sym))
  }

  pub fn new_u64(context: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(SymU64::new(context, prefix)))
  }

  pub fn from_u128(context: &'ctx Context, value: u128) -> Self {
    SymValue(SymValueImpl::U128(SymU128::from(context, value)))
  }

  pub fn from_sym_u128(sym: SymU128<'ctx>) -> Self {
    SymValue(SymValueImpl::U128(sym))
  }

  pub fn new_u128(context: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(SymU128::new(context, prefix)))
  }

  pub fn from_bool(context: &'ctx Context, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::from(context, value)))
  }

  pub fn from_sym_bool(sym: SymBool<'ctx>) -> Self {
    SymValue(SymValueImpl::Bool(sym))
  }

  pub fn new_bool(context: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::new(context, prefix)))
  }

  pub fn from_address(context: &'ctx Context, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(
      context, address,
    )))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn from_signer(context: &'ctx Context, signer: AccountAddress) -> Self {
    SymValue(SymValueImpl::Signer(SymAccountAddress::new(context, signer)))
  }

  pub fn from_sym_signer(signer: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Signer(signer))
  }

  pub fn from_deserialized_struct(
    context: &'ctx Context,
    s: Struct,
    ty: &FatStructType,
  ) -> VMResult<Self> {
    let fields: Vec<SymValue> = s
      .unpack()?
      .into_iter()
      .enumerate()
      .map(|(idx, v)| SymValue::from_deserialized_value(context, v, &ty.layout[idx]))
      .collect::<VMResult<_>>()?;
    Ok(SymValue::from_sym_struct(SymStruct::pack(context, &ty, fields)?))
  }

  pub fn from_sym_struct(s: SymStruct<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(s.0))
  }

  pub(super) fn from_sym_vector(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(SymContainer::Vector(v)))
  }

  pub(super) fn from_sym_vec_u8(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(SymContainer::VecU8(v)))
  }

  pub(super) fn from_sym_vec_u64(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(SymContainer::VecU64(v)))
  }

  pub(super) fn from_sym_vec_u128(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(SymContainer::VecU128(v)))
  }

  pub(super) fn from_sym_vec_bool(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(SymContainer::VecBool(v)))
  }

  // TODO: consider whether we want to replace these with fn vector(v: Vec<Value>).
  // pub fn vector_u8(it: impl IntoIterator<Item = u8>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainer::U8(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_u64(it: impl IntoIterator<Item = u64>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainer::U64(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_u128(it: impl IntoIterator<Item = u128>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainer::U128(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_bool(it: impl IntoIterator<Item = bool>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainer::Bool(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_address(it: impl IntoIterator<Item = SymAccountAddress<'ctx>>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainer::General(
  //     it.into_iter().map(SymValueImpl::Address).collect(),
  //   )))
  // }
}

// impl<'ctx> SymContainer<'ctx> {
//   pub fn general(context: &'ctx Context, vec: Vec<SymValueImpl<'ctx>>) -> Self {
//     SymContainer {
//       context,
//       container: SymContainer::General(vec),
//     }
//   }

//   pub fn u8(context: &'ctx Context, vec: Vec<SymU8<'ctx>>) -> Self {
//     SymContainer {
//       context,
//       container: SymContainer::U8(vec),
//     }
//   }

//   pub fn u64(context: &'ctx Context, vec: Vec<SymU64<'ctx>>) -> Self {
//     SymContainer {
//       context,
//       container: SymContainer::U64(vec),
//     }
//   }

//   pub fn u128(context: &'ctx Context, vec: Vec<SymU128<'ctx>>) -> Self {
//     SymContainer {
//       context,
//       container: SymContainer::U128(vec),
//     }
//   }
  
//   pub fn bool(context: &'ctx Context, vec: Vec<SymBool<'ctx>>) -> Self {
//     SymContainer {
//       context,
//       container: SymContainer::Bool(vec),
//     }
//   }
// }

/***************************************************************************************
*
* Casting
*
*   Due to the public value types being opaque to an external user, the following
*   public APIs are required to enable conversion between types in order to gain access
*   to specific operations certain more refined types offer.
*   For example, one must convert a `Value` to a `Struct` before unpack can be called.
*
*   It is expected that the caller will keep track of the invariants and guarantee
*   the conversion will succeed. An error will be raised in case of a violation.
*
**************************************************************************************/
pub trait VMSymValueCast<T> {
  fn cast(self) -> VMResult<T>;
}

macro_rules! impl_vm_sym_value_cast {
  ($ty: ty, $tc: ident) => {
    impl<'ctx> VMSymValueCast<$ty> for SymValue<'ctx> {
      fn cast(self) -> VMResult<$ty> {
        match self.0 {
          SymValueImpl::$tc(x) => Ok(x),
          v => Err(
            VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
              "cannot cast {:?} to {}",
              v,
              stringify!($ty)
            )),
          ),
        }
      }
    }
  };
}

// !!!
impl_vm_sym_value_cast!(SymU8<'ctx>, U8);
impl_vm_sym_value_cast!(SymU64<'ctx>, U64);
impl_vm_sym_value_cast!(SymU128<'ctx>, U128);
impl_vm_sym_value_cast!(SymBool<'ctx>, Bool);
impl_vm_sym_value_cast!(SymAccountAddress<'ctx>, Address);
impl_vm_sym_value_cast!(SymContainerRef<'ctx>, ContainerRef);
impl_vm_sym_value_cast!(SymIndexedRef<'ctx>, IndexedRef);

impl<'ctx> VMSymValueCast<SymIntegerValue<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymIntegerValue<'ctx>> {
    match self.0 {
      SymValueImpl::U8(x) => Ok(SymIntegerValue::U8(x)),
      SymValueImpl::U64(x) => Ok(SymIntegerValue::U64(x)),
      SymValueImpl::U128(x) => Ok(SymIntegerValue::U128(x)),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to integer", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymReference<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymReference<'ctx>> {
    match self.0 {
      SymValueImpl::ContainerRef(r) => Ok(SymReference(SymReferenceImpl::ContainerRef(r))),
      SymValueImpl::IndexedRef(r) => Ok(SymReference(SymReferenceImpl::IndexedRef(r))),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to reference", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymContainer<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymContainer<'ctx>> {
    match self.0 {
      SymValueImpl::Container(r) => take_unique_ownership(r),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to container", v,)),
      ),
    }
  }
}

// ???
// impl<'ctx> VMSymValueCast<Vec<SymValue<'ctx>>> for SymValue<'ctx> {
//   fn cast(self) -> VMResult<Vec<SymValue<'ctx>>> {
//     match self.0 {
//       SymValueImpl::Container(r) => Ok(match take_unique_ownership(r)?.container {
//         SymContainer::General(vs) => vs.into_iter().map(SymValue).collect(),
//         SymContainer::U8(vs) => vs.into_iter().map(SymValue::from_sym_u8).collect(),
//         SymContainer::U64(vs) => vs.into_iter().map(SymValue::from_sym_u64).collect(),
//         SymContainer::U128(vs) => vs.into_iter().map(SymValue::from_sym_u128).collect(),
//         SymContainer::Bool(vs) => vs.into_iter().map(SymValue::from_sym_bool).collect(),
//       }),
//       v => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
//           .with_message(format!("cannot cast {:?} to vector of values", v,)),
//       ),
//     }
//   }
// }

impl<'ctx> VMSymValueCast<SymStruct<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymStruct<'ctx>> {
    match self.0 {
      SymValueImpl::Container(r) => Ok(SymStruct(take_unique_ownership(r)?)),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to struct", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymStructRef<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymStructRef<'ctx>> {
    Ok(SymStructRef(VMSymValueCast::cast(self)?))
  }
}

// impl<'ctx> VMSymValueCast<Vec<SymU8<'ctx>>> for SymValue<'ctx> {
//   fn cast(self) -> VMResult<Vec<SymU8<'ctx>>> {
//     match self.0 {
//       SymValueImpl::Container(r) => match take_unique_ownership(r)?.container {
//         SymContainer::U8(v) => Ok(v),
//         v => Err(
//           VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
//             .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
//         ),
//       },
//       v => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
//           .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
//       ),
//     }
//   }
// }

impl<'ctx> SymValue<'ctx> {
  pub fn value_as<T>(self) -> VMResult<T>
  where
    Self: VMSymValueCast<T>,
  {
    VMSymValueCast::cast(self)
  }
}

impl<'ctx> VMSymValueCast<SymU8<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> VMResult<SymU8<'ctx>> {
    match self {
      Self::U8(x) => Ok(x),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u8", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymU64<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> VMResult<SymU64<'ctx>> {
    match self {
      Self::U64(x) => Ok(x),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u64", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymU128<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> VMResult<SymU128<'ctx>> {
    match self {
      Self::U128(x) => Ok(x),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u128", v,)),
      ),
    }
  }
}

impl<'ctx> SymIntegerValue<'ctx> {
  pub fn value_as<T>(self) -> VMResult<T>
  where
    Self: VMSymValueCast<T>,
  {
    VMSymValueCast::cast(self)
  }
}

/***************************************************************************************
*
* Integer Operations
*
*   Arithmetic operations and conversions for integer values.
*
**************************************************************************************/
impl<'ctx> SymIntegerValue<'ctx> {
  pub fn add(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::add(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::add(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::add(l, r))),
      (l, r) => {
        let msg = format!("Cannot add {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn sub(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::sub(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::sub(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::sub(l, r))),
      (l, r) => {
        let msg = format!("Cannot sub {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn mul(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::mul(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::mul(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::mul(l, r))),
      (l, r) => {
        let msg = format!("Cannot mul {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn div(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::div(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::div(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::div(l, r))),
      (l, r) => {
        let msg = format!("Cannot div {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn rem(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    let res = match (&self, &other) {
      (U8(l), U8(r)) => Some(SymIntegerValue::U8(SymU8::rem(l, r))),
      (U64(l), U64(r)) => Some(SymIntegerValue::U64(SymU64::rem(l, r))),
      (U128(l), U128(r)) => Some(SymIntegerValue::U128(SymU128::rem(l, r))),
      (l, r) => {
        let msg = format!("Cannot rem {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    };
    res.ok_or_else(|| VMStatus::new(StatusCode::ARITHMETIC_ERROR))
  }

  pub fn bit_or(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_or(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_or(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_or(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_or {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_and(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_and(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_and(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_and(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_and {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_xor(self, other: Self) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_xor(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_xor(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_xor(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_xor {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn shl(self, n_bits: SymU8<'ctx>) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shl(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shl(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shl(&n_bits)),
    })
  }

  pub fn shr(self, n_bits: SymU8<'ctx>) -> VMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shr(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shr(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shr(&n_bits)),
    })
  }

  pub fn lt(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::lt(l, r),
      (U64(l), U64(r)) => SymU64::lt(l, r),
      (U128(l), U128(r)) => SymU128::lt(l, r),
      (l, r) => {
        let msg = format!("Cannot lt {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn le(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::le(l, r),
      (U64(l), U64(r)) => SymU64::le(l, r),
      (U128(l), U128(r)) => SymU128::le(l, r),
      (l, r) => {
        let msg = format!("Cannot le {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn gt(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::gt(l, r),
      (U64(l), U64(r)) => SymU64::gt(l, r),
      (U128(l), U128(r)) => SymU128::gt(l, r),
      (l, r) => {
        let msg = format!("Cannot gt {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn ge(self, other: Self) -> VMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::ge(l, r),
      (U64(l), U64(r)) => SymU64::ge(l, r),
      (U128(l), U128(r)) => SymU128::ge(l, r),
      (l, r) => {
        let msg = format!("Cannot ge {:?} and {:?}", l, r);
        return Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn into_value(self) -> SymValue<'ctx> {
    use SymIntegerValue::*;

    match self {
      U8(x) => SymValue::from_sym_u8(x),
      U64(x) => SymValue::from_sym_u64(x),
      U128(x) => SymValue::from_sym_u128(x),
    }
  }
}

impl<'ctx> SymIntegerValue<'ctx> {
  // code from libra
  // pub fn cast_u8(self) -> VMResult<u8> {
  //   use SymIntegerValue::*;

  //   match self {
  //     U8(x) => Ok(x),
  //     U64(x) => {
  //       if x > (std::u8::MAX as u64) {
  //         Err(
  //           VMStatus::new(StatusCode::ARITHMETIC_ERROR)
  //             .with_message(format!("Cannot cast u64({}) to u8", x)),
  //         )
  //       } else {
  //         Ok(x as u8)
  //       }
  //     }
  //     U128(x) => {
  //       if x > (std::u8::MAX as u128) {
  //         Err(
  //           VMStatus::new(StatusCode::ARITHMETIC_ERROR)
  //             .with_message(format!("Cannot cast u128({}) to u8", x)),
  //         )
  //       } else {
  //         Ok(x as u8)
  //       }
  //     }
  //   }
  // }

  // pub fn cast_u64(self) -> VMResult<u64> {
  //   use SymIntegerValue::*;

  //   match self {
  //     U8(x) => Ok(x as u64),
  //     U64(x) => Ok(x),
  //     U128(x) => {
  //       if x > (std::u64::MAX as u128) {
  //         Err(
  //           VMStatus::new(StatusCode::ARITHMETIC_ERROR)
  //             .with_message(format!("Cannot cast u128({}) to u64", x)),
  //         )
  //       } else {
  //         Ok(x as u64)
  //       }
  //     }
  //   }
  // }

  // pub fn cast_u128(self) -> VMResult<u128> {
  //   use SymIntegerValue::*;

  //   Ok(match self {
  //     U8(x) => x as u128,
  //     U64(x) => x as u128,
  //     U128(x) => x,
  //   })
  // }

  // Original code
  // !!!
  // Revise: should check?

  pub fn cast_u8(self) -> SymU8<'ctx> {
    use SymIntegerValue::*;
    match self {
      U8(x) => x,
      U64(x) => x.cast_u8(),
      U128(x) => x.cast_u8(),
    }
  }

  pub fn cast_u64(self) -> SymU64<'ctx> {
    use SymIntegerValue::*;
    match self {
      U8(x) => x.cast_u64(),
      U64(x) => x,
      U128(x) => x.cast_u64(),
    }
  }

  pub fn cast_u128(self) -> SymU128<'ctx> {
    use SymIntegerValue::*;
    match self {
      U8(x) => x.cast_u128(),
      U64(x) => x.cast_u128(),
      U128(x) => x,
    }
  }
}

/***************************************************************************************
*
* Gas
*
*   Abstract memory sizes of the VM values.
*
**************************************************************************************/

impl<'ctx> SymContainer<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    use SymContainer::*;

    match &self {
      Locals { locals: v, .. } => v
        .iter()
        .fold(STRUCT_SIZE, |acc, v| acc.map2(v.size(), Add::add)),
      // !!! figure it out
      // Struct(v) => AbstractMemorySize::new((v.len() * size_of::<u8>()) as u64),
      // Vector(v) => AbstractMemorySize::new((v.len() * size_of::<u8>()) as u64),
      // VecU8(v) => AbstractMemorySize::new((v.len() * size_of::<u8>()) as u64),
      // VecU64(v) => AbstractMemorySize::new((v.len() * size_of::<u64>()) as u64),
      // VecU128(v) => AbstractMemorySize::new((v.len() * size_of::<u128>()) as u64),
      // VecBool(v) => AbstractMemorySize::new((v.len() * size_of::<bool>()) as u64),
      _ => AbstractMemorySize::new(0),
    }
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    words_in(REFERENCE_SIZE)
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    words_in(REFERENCE_SIZE)
  }
}

impl<'ctx> SymValueImpl<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    use SymValueImpl::*;

    match self {
      Invalid | U8(_) | U64(_) | U128(_) | Bool(_) => CONST_SIZE,
      Address(_) | Signer(_) => AbstractMemorySize::new(SymAccountAddress::LENGTH as u64),
      ContainerRef(r) => r.size(),
      IndexedRef(r) => r.size(),
      // TODO: in case the borrow fails the VM will panic.
      Container(r) => r.borrow().size(),
    }
  }
}

impl<'ctx> SymStruct<'ctx> {
  pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
    self.0.size()
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
    self.0.size()
  }
}

impl<'ctx> SymReferenceImpl<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    match self {
      Self::ContainerRef(r) => r.size(),
      Self::IndexedRef(r) => r.size(),
    }
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
    self.0.size()
  }
}

impl<'ctx> SymGlobalValue<'ctx> {
  pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
    // TODO: should it be self.container.borrow().size()
    words_in(REFERENCE_SIZE)
  }
}

/***************************************************************************************
*
* Struct Operations
*
*   Public APIs for Struct.
*
**************************************************************************************/
impl<'ctx> SymStruct<'ctx> {
  pub fn pack<I: IntoIterator<Item = SymValue<'ctx>>>(context: &'ctx Context, ty: &FatStructType, vals: I) -> VMResult<Self> {
    Ok(Self(SymContainer::Struct(SymStructImpl::pack(context, ty, vals)?)))
  }

  pub fn unpack(self) -> VMResult<impl Iterator<Item = SymValue<'ctx>>> {
    match self.0 {
      SymContainer::Struct(v) => Ok(v.unpack()?.into_iter()),
      _ => Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("not a struct".to_string()),
      ),
    }
  }
}

/***************************************************************************************
*
* Global Value Operations
*
*   Public APIs for GlobalValue. They allow global values to be created from external
*   source (a.k.a. storage), and references to be taken from them. At the end of the
*   transaction execution the dirty ones can be identified and wrote back to storage.
*
**************************************************************************************/
impl<'ctx> SymGlobalValue<'ctx> {
  pub fn new(v: SymValue<'ctx>) -> VMResult<Self> {
    match v.0 {
      SymValueImpl::Container(container) => {
        // TODO: check strong count?
        Ok(Self {
          status: Rc::new(RefCell::new(GlobalDataStatus::Clean)),
          container,
        })
      }
      v => Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot create global ref from {:?}", v)),
      ),
    }
  }

  pub fn borrow_global(&self) -> VMResult<SymValue<'ctx>> {
    Ok(SymValue(SymValueImpl::ContainerRef(
      SymContainerRef::Global {
        status: Rc::clone(&self.status),
        container: Rc::clone(&self.container),
        location: None,
      },
    )))
  }

  pub fn mark_dirty(&self) -> VMResult<()> {
    *self.status.borrow_mut() = GlobalDataStatus::Dirty;
    Ok(())
  }

  pub fn is_clean(&self) -> VMResult<bool> {
    match &*self.status.borrow() {
      GlobalDataStatus::Clean => Ok(true),
      _ => Ok(false),
    }
  }

  pub fn is_dirty(&self) -> VMResult<bool> {
    match &*self.status.borrow() {
      GlobalDataStatus::Dirty => Ok(true),
      _ => Ok(false),
    }
  }

  pub fn into_owned_struct(self) -> VMResult<SymStruct<'ctx>> {
    Ok(SymStruct(take_unique_ownership(self.container)?))
  }

  pub fn clone_for_symbolic_state_fork(&self) -> Self {
    SymGlobalValue {
      status: Rc::new(RefCell::new(self.status.borrow().clone())),
      container: Rc::new(RefCell::new(self.container.borrow().copy_value()))
    }
  }
}

/***************************************************************************************
*
* Display
*
*   Implementation of the Display trait for VM Values. These are supposed to be more
*   friendly & readable than the generated Debug dump.
*
**************************************************************************************/

impl<'ctx> Display for SymValueImpl<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::Invalid => write!(f, "Invalid"),

      Self::U8(x) => write!(f, "SymU8({})", x),
      Self::U64(x) => write!(f, "SymU64({})", x),
      Self::U128(x) => write!(f, "SymU128({})", x),
      Self::Bool(x) => write!(f, "SymBool({})", x),
      Self::Address(addr) => write!(f, "SymAddress({:?})", addr),
      Self::Signer(addr) => write!(f, "SymSigner({:?})", addr),

      Self::Container(r) => write!(f, "SymContainer({})", &*r.borrow()),

      Self::ContainerRef(r) => write!(f, "{}", r),
      Self::IndexedRef(r) => write!(f, "{}", r),
    }
  }
}

fn display_list_of_items<T, I>(items: I, f: &mut fmt::Formatter) -> fmt::Result
where
  T: Display,
  I: IntoIterator<Item = T>,
{
  write!(f, "[")?;
  let mut items = items.into_iter();
  if let Some(x) = items.next() {
    write!(f, "{}", x)?;
    for x in items {
      write!(f, ", {}", x)?;
    }
  }
  write!(f, "]")
}

impl<'ctx> Display for SymContainerRef<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    // TODO: this could panic.
    match self {
      Self::Local { container, location } => {
        let loc = match location {
          Some(l) => format!(" @ {}", l.as_ref()),
          None => "".to_string(),
        };
        write!(f, "({}, {}{})", Rc::strong_count(container), &*container.borrow(), loc)
      },
      Self::Global { status, container, location } => {
        let loc = match location {
          Some(l) => format!(" @ {}", l.as_ref()),
          None => "".to_string(),
        };
        write!(
          f,
          "({:?}, {}, {}{})",
          &*status.borrow(),
          Rc::strong_count(container),
          &*container.borrow(),
          loc,
        )
      },
    }
  }
}

impl<'ctx> Display for SymIndexedRef<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}<{:?}>", self.container_ref, self.idx)
  }
}

impl<'ctx> Display for SymContainer<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use SymContainer::*;
    match &self {
      Locals { locals: v, .. } => display_list_of_items(v, f),
      Struct(v) => write!(f, "{:?}", v),
      Vector(v) => write!(f, "{:?}", v),
      VecU8(v) => write!(f, "{:?}", v),
      VecU64(v) => write!(f, "{:?}", v),
      VecU128(v) => write!(f, "{:?}", v),
      VecBool(v) => write!(f, "{:?}", v),
    }
  }
}

impl<'ctx> Display for SymValue<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    Display::fmt(&self.0, f)
  }
}

// #[allow(dead_code)]
// pub mod debug {
//   use super::*;
//   use crate::{loaded_data::runtime_types::Type, natives::function::NativeContext};
//   use move_core_types::gas_schedule::ZERO_GAS_UNITS;
//   use std::fmt::Write;

//   fn print_value_impl<B: Write>(buf: &mut B, ty: &FatType, val: &SymValueImpl<'ctx>) -> VMResult<()> {
//     match (ty, val) {
//       (FatType::U8, SymValueImpl::U8(x)) => debug_write!(buf, "{}u8", x),
//       (FatType::U64, SymValueImpl::U64(x)) => debug_write!(buf, "{}u64", x),
//       (FatType::U128, SymValueImpl::U128(x)) => debug_write!(buf, "{}u128", x),
//       (FatType::Bool, SymValueImpl::Bool(x)) => debug_write!(buf, "{}", x),
//       (FatType::Address, SymValueImpl::Address(x)) => debug_write!(buf, "{}", x),

//       (FatType::Vector(elem_ty), SymValueImpl::Container(r)) => {
//         print_vector(buf, elem_ty, &*r.borrow())
//       }

//       (FatType::Struct(struct_ty), SymValueImpl::Container(r)) => {
//         print_struct(buf, struct_ty, &*r.borrow())
//       }

//       (FatType::MutableReference(val_ty), SymValueImpl::ContainerRef(r)) => {
//         debug_write!(buf, "(&mut) ")?;
//         print_container_ref(buf, val_ty, r)
//       }
//       (FatType::Reference(val_ty), SymValueImpl::ContainerRef(r)) => {
//         debug_write!(buf, "(&) ")?;
//         print_container_ref(buf, val_ty, r)
//       }

//       (FatType::MutableReference(val_ty), SymValueImpl::IndexedRef(r)) => {
//         debug_write!(buf, "(&mut) ")?;
//         print_indexed_ref(buf, val_ty, r)
//       }
//       (FatType::Reference(val_ty), SymValueImpl::IndexedRef(r)) => {
//         debug_write!(buf, "(&) ")?;
//         print_indexed_ref(buf, val_ty, r)
//       }

//       (_, SymValueImpl::Invalid) => debug_write!(buf, "(invalid)"),

//       _ => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
//           .with_message(format!("cannot print value {:?} as type {:?}", val, ty)),
//       ),
//     }
//   }

//   fn print_vector<B: Write>(buf: &mut B, elem_ty: &FatType, v: &Container) -> VMResult<()> {
//     macro_rules! print_vector {
//       ($v: expr, $suffix: expr) => {{
//         let suffix = &$suffix;
//         debug_write!(buf, "[")?;
//         let mut it = $v.iter();
//         if let Some(x) = it.next() {
//           debug_write!(buf, "{}{}", x, suffix)?;
//           for x in it {
//             debug_write!(buf, ", {}{}", x, suffix)?;
//           }
//         }
//         debug_write!(buf, "]")
//       }};
//     }

//     match (elem_ty, v) {
//       (FatType::U8, Container::U8(v)) => print_vector!(v, "u8"),
//       (FatType::U64, Container::U64(v)) => print_vector!(v, "u64"),
//       (FatType::U128, Container::U128(v)) => print_vector!(v, "u128"),
//       (FatType::Bool, Container::Bool(v)) => print_vector!(v, ""),

//       (FatType::Address, Container::General(v)) | (FatType::Struct(_), Container::General(v)) => {
//         debug_write!(buf, "[")?;
//         let mut it = v.iter();
//         if let Some(x) = it.next() {
//           print_value_impl(buf, elem_ty, x)?;
//           for x in it {
//             debug_write!(buf, ", ")?;
//             print_value_impl(buf, elem_ty, x)?;
//           }
//         }
//         debug_write!(buf, "]")
//       }

//       _ => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
//           "cannot print container {:?} as vector with element type {:?}",
//           v, elem_ty
//         )),
//       ),
//     }
//   }

//   fn print_struct<B: Write>(buf: &mut B, struct_ty: &FatStructType, s: &Container) -> VMResult<()> {
//     let v = match s {
//       Container::General(v) => v,
//       _ => {
//         return Err(
//           VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
//             .with_message(format!("invalid container {:?} as struct", s)),
//         )
//       }
//     };
//     let layout = &struct_ty.layout;
//     if layout.len() != v.len() {
//       return Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
//           "cannot print container {:?} as struct type {:?}, expected {} fields, got {}",
//           v,
//           struct_ty,
//           layout.len(),
//           v.len()
//         )),
//       );
//     }
//     debug_write!(buf, "{}::{} {{ ", struct_ty.module, struct_ty.name)?;
//     let mut it = layout.iter().zip(v.iter());
//     if let Some((ty, val)) = it.next() {
//       print_value_impl(buf, ty, val)?;
//       for (ty, val) in it {
//         debug_write!(buf, ", ")?;
//         print_value_impl(buf, ty, val)?;
//       }
//     }
//     debug_write!(buf, " }}")
//   }

//   fn print_container_ref<B: Write>(
//     buf: &mut B,
//     val_ty: &FatType,
//     r: &ContainerRef,
//   ) -> VMResult<()> {
//     match val_ty {
//       FatType::Vector(elem_ty) => print_vector(buf, elem_ty, &*r.borrow()),
//       FatType::Struct(struct_ty) => print_struct(buf, struct_ty, &*r.borrow()),
//       _ => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
//           "cannot print container {:?} as type {:?}",
//           &*r.borrow(),
//           val_ty
//         )),
//       ),
//     }
//   }

//   fn print_indexed_ref<B: Write>(buf: &mut B, val_ty: &FatType, r: &IndexedRef) -> VMResult<()> {
//     macro_rules! print_vector_elem {
//       ($v: expr, $idx: expr, $suffix: expr) => {
//         match $v.get($idx) {
//           Some(x) => debug_write!(buf, "{}{}", x, $suffix),
//           None => Err(
//             VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//               .with_message("ref index out of bounds".to_string()),
//           ),
//         }
//       };
//     }

//     let idx = r.idx;
//     match (val_ty, &*r.container_ref.borrow()) {
//       (FatType::U8, Container::U8(v)) => print_vector_elem!(v, idx, "u8"),
//       (FatType::U64, Container::U64(v)) => print_vector_elem!(v, idx, "u64"),
//       (FatType::U128, Container::U128(v)) => print_vector_elem!(v, idx, "u128"),
//       (FatType::Bool, Container::Bool(v)) => print_vector_elem!(v, idx, ""),

//       (FatType::U8, Container::General(v))
//       | (FatType::U64, Container::General(v))
//       | (FatType::U128, Container::General(v))
//       | (FatType::Bool, Container::General(v))
//       | (FatType::Address, Container::General(v)) => match v.get(idx) {
//         Some(val) => print_value_impl(buf, val_ty, val),
//         None => Err(
//           VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//             .with_message("ref index out of bounds".to_string()),
//         ),
//       },

//       (_, container) => Err(
//         VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
//           "cannot print element {} of container {:?} as {:?}",
//           idx, container, val_ty
//         )),
//       ),
//     }
//   }

//   fn print_reference<B: Write>(buf: &mut B, val_ty: &FatType, r: &Reference) -> VMResult<()> {
//     match &r.0 {
//       ReferenceImpl::ContainerRef(r) => print_container_ref(buf, val_ty, r),
//       ReferenceImpl::IndexedRef(r) => print_indexed_ref(buf, val_ty, r),
//     }
//   }

//   pub fn print_locals<B: Write>(buf: &mut B, tys: &[FatType], locals: &Locals) -> VMResult<()> {
//     match &*locals.0.borrow() {
//       Container::General(v) => {
//         // TODO: The number of spaces in the indent is currently hard coded.
//         // Plan is to switch to the pretty crate for pretty printing.
//         if tys.is_empty() {
//           debug_writeln!(buf, "            (none) ")?;
//         } else {
//           for (idx, (ty, val)) in tys.iter().zip(v.iter()).enumerate() {
//             debug_write!(buf, "            [{}] ", idx)?;
//             print_value_impl(buf, ty, val)?;
//             debug_writeln!(buf)?;
//           }
//         }
//         Ok(())
//       }
//       _ => unreachable!(),
//     }
//   }

//   #[allow(unused_mut)]
//   #[allow(unused_variables)]
//   pub fn native_print(
//     context: &mut impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 1);

//     // No-op if the feature flag is not present.
//     #[cfg(feature = "debug_module")]
//     {
//       let mut ty_args = context.convert_to_fat_types(ty_args)?;
//       let ty = ty_args.pop().unwrap();
//       let r: Reference = args.pop_back().unwrap().value_as()?;

//       let mut buf = String::new();
//       print_reference(&mut buf, &ty, &r)?;
//       println!("[debug] {}", buf);
//     }

//     Ok(SymNativeResult::ok(ZERO_GAS_UNITS, vec![]))
//   }

//   #[allow(unused_variables)]
//   pub fn native_print_stack_trace(
//     context: &mut impl NativeContext,
//     ty_args: Vec<Type>,
//     mut _arguments: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.is_empty());

//     #[cfg(feature = "debug_module")]
//     {
//       let mut s = String::new();
//       context.print_stack_trace(&mut s)?;
//       println!("{}", s);
//     }

//     Ok(SymNativeResult::ok(ZERO_GAS_UNITS, vec![]))
//   }
// }

/***************************************************************************************
*
* Constants
*
*   Implementation of deseserialization of constant data into a runtime value
*
**************************************************************************************/

impl<'ctx> SymValue<'ctx> {
  fn constant_sig_token_to_type(constant_signature: &SignatureToken) -> Option<FatType> {
    use FatType as T;
    use SignatureToken as S;
    Some(match constant_signature {
      S::Bool => T::Bool,
      S::U8 => T::U8,
      S::U64 => T::U64,
      S::U128 => T::U128,
      S::Address => T::Address,
      S::Signer => T::Signer,
      S::Vector(inner) => T::Vector(Box::new(Self::constant_sig_token_to_type(inner)?)),
      // Not yet supported
      S::Struct(_) | S::StructInstantiation(_, _) => return None,
      // Not allowed/Not meaningful
      S::TypeParameter(_) | S::Reference(_) | S::MutableReference(_) => return None,
    })
  }

  pub fn deserialize_constant(context: &'ctx Context, constant: &Constant) -> Option<SymValue<'ctx>> {
    let ty = Self::constant_sig_token_to_type(&constant.type_)?;
    let v = Value::simple_deserialize(&constant.data, &ty).ok()?;
    SymValue::from_deserialized_value(context, v, &ty).ok()
  }

  // pub fn serialize_constant(type_: SignatureToken, value: Value) -> Option<Constant> {
  //   let ty = Self::constant_sig_token_to_type(&type_)?;
  //   let data = value.simple_serialize(&ty)?;
  //   Some(Constant { data, type_ })
  // }
}

/***************************************************************************************
*
* SymbolicMoveValue
*
**************************************************************************************/

impl<'ctx> SymbolicMoveValue<'ctx> for SymContainer<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    use SymContainer::*;

    match &self {
      Locals { .. } => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
      Struct(s) => Ok(s.as_ast()?),
      Vector(v) | VecU8(v) | VecU64(v) | VecU128(v) | VecBool(v) => {
        Ok(v.as_ast()?)
      }
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymValueImpl<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    use SymValueImpl::*;
  
    match self {
      Invalid => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
    
      U8(v) => Ok(v.as_ast()?),
      U64(v) => Ok(v.as_ast()?),
      U128(v) => Ok(v.as_ast()?),
      Bool(v) => Ok(v.as_ast()?),
      Address(v) => Ok(v.as_ast()?),
      Signer(v) => Ok(v.as_ast()?),
    
      Container(c) => Ok(c.borrow().as_ast()?),
    
      ContainerRef(_) => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
      IndexedRef(_) => Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymValue<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(self.0.as_ast()?)
  }
}