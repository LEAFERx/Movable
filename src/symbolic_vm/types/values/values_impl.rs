// use crate::{
//   gas_schedule::NativeCostIndex,
//   loaded_data::types::{FatStructType, FatType},
//   natives::function::{native_gas, NativeResult},
// };
use libra_types::{
  account_address::AccountAddress,
  vm_error::{sub_status::NFE_VECTOR_ERROR_BASE, StatusCode, VMStatus},
};
use move_core_types::gas_schedule::{
  words_in, AbstractMemorySize, GasAlgebra, GasCarrier, CONST_SIZE, REFERENCE_SIZE, STRUCT_SIZE,
};
use std::{
  cell::{Ref, RefCell, RefMut},
  // collections::VecDeque,
  fmt::{self, Debug, Display},
  iter,
  // mem::size_of,
  ops::Add,
  rc::Rc,
};
use vm::{
  errors::*,
  file_format::{Constant, SignatureToken},
};

use z3::ast::Dynamic;

use crate::{
  engine::solver::Solver,
  symbolic_vm::types::values::{
    account_address::SymAccountAddress,
    primitives::{SymBool, SymU128, SymU64, SymU8},
  }
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
enum SymValueImpl<'ctx> {
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
#[derive(Debug)]
enum SymContainerImpl<'ctx> {
  General(Vec<SymValueImpl<'ctx>>),
  U8(Vec<SymU8<'ctx>>),
  U64(Vec<SymU64<'ctx>>),
  U128(Vec<SymU128<'ctx>>),
  Bool(Vec<SymBool<'ctx>>),
}

#[derive(Debug)]
struct SymContainer<'ctx> {
  solver: &'ctx Solver<'ctx>,
  container: SymContainerImpl<'ctx>,
}

/// A ContainerRef is a direct reference to a container, which could live either in the frame
/// or in global storage. In the latter case, it also keeps a status flag indicating whether
/// the container has been possibly modified.
#[derive(Debug)]
enum SymContainerRef<'ctx> {
  Local(Rc<RefCell<SymContainer<'ctx>>>),
  Global {
    status: Rc<RefCell<GlobalDataStatus>>,
    container: Rc<RefCell<SymContainer<'ctx>>>,
  },
}

/// Status for global (on-chain) data:
/// Clean - the data was only read.
/// Dirty - the data was possibly modified.
#[derive(Debug, Clone, Copy)]
enum GlobalDataStatus {
  Clean,
  Dirty,
}

/// A Move reference pointing to an element in a container.
#[derive(Debug)]
struct SymIndexedRef<'ctx> {
  idx: usize,
  container_ref: SymContainerRef<'ctx>,
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
pub struct SymValue<'ctx>(SymValueImpl<'ctx>);

/// The locals for a function frame. It allows values to be read, written or taken
/// reference from.
#[derive(Debug)]
pub struct SymLocals<'ctx>(Rc<RefCell<SymContainer<'ctx>>>);

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
impl<'ctx> SymContainerImpl<'ctx> {
  fn len(&self) -> usize {
    use SymContainerImpl::*;

    match self {
      General(v) => v.len(),
      U8(v) => v.len(),
      U64(v) => v.len(),
      U128(v) => v.len(),
      Bool(v) => v.len(),
    }
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn len(&self) -> usize {
    self.container.len()
  }
}

impl<'ctx> SymValueImpl<'ctx> {
  fn into_ast(self) -> VMResult<Dynamic<'ctx>> {
    match self {
      SymValueImpl::U8(u) => Ok(u.collect()),
      SymValueImpl::U64(u) => Ok(u.collect()),
      SymValueImpl::U128(u) => Ok(u.collect()),
      SymValueImpl::Bool(b) => Ok(b.collect()),
      _ => {
        let msg = format!("Cannot convert {:?} to ast.", self);
        Err(VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg))
      }
    }
  }
  fn new_container(container: SymContainer<'ctx>) -> Self {
    Self::Container(Rc::new(RefCell::new(container)))
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn into_ast(self) -> VMResult<Dynamic<'ctx>> {
    self.0.into_ast()
  }

  pub fn is_valid_script_arg(&self, sig: &SignatureToken) -> bool {
    match (sig, &self.0) {
      (SignatureToken::U8, SymValueImpl::U8(_)) => true,
      (SignatureToken::U64, SymValueImpl::U64(_)) => true,
      (SignatureToken::U128, SymValueImpl::U128(_)) => true,
      (SignatureToken::Bool, SymValueImpl::Bool(_)) => true,
      (SignatureToken::Address, SymValueImpl::Address(_)) => true,
      (SignatureToken::Vector(ty), SymValueImpl::Container(r)) => match (&**ty, &(*r.borrow()).container) {
        (SignatureToken::U8, SymContainerImpl::U8(_)) => true,
        _ => false,
      },
      _ => false,
    }
  }
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
  fn borrow(&self) -> Ref<SymContainer<'ctx>> {
    match self {
      Self::Local(container) | Self::Global { container, .. } => container.borrow(),
    }
  }

  fn borrow_mut(&self) -> RefMut<SymContainer<'ctx>> {
    match self {
      Self::Local(container) => container.borrow_mut(),
      Self::Global { container, status } => {
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

impl<'ctx> SymValueImpl<'ctx> {
  fn as_value_ref<T>(&self) -> VMResult<&T>
  where
    Self: VMValueRef<T>,
  {
    VMValueRef::value_ref(self)
  }
}

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
  fn copy_value(&self) -> Self {
    use SymValueImpl::*;

    match self {
      Invalid => Invalid,

      U8(x) => U8(*x),
      U64(x) => U64(*x),
      U128(x) => U128(*x),
      Bool(x) => Bool(*x),
      Address(x) => Address(*x),
      // TODO copying resource?
      Signer(x) => Signer(*x),

      ContainerRef(r) => ContainerRef(r.copy_value()),
      IndexedRef(r) => IndexedRef(r.copy_value()),

      // When cloning a container, we need to make sure we make a deep
      // copy of the data instead of a shallow copy of the Rc.
      Container(c) => Container(Rc::new(RefCell::new(c.borrow().copy_value()))),
    }
  }
}

impl<'ctx> SymContainerImpl<'ctx> {
  fn copy_value(&self) -> Self {
    use SymContainerImpl::*;

    match self {
      General(v) => General(v.iter().map(|x| x.copy_value()).collect()),
      U8(v) => U8(v.clone()),
      U64(v) => U64(v.clone()),
      U128(v) => U128(v.clone()),
      Bool(v) => Bool(v.clone()),
    }
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn copy_value(&self) -> Self {
    Self {
      solver: self.solver,
      container: self.container.copy_value(),
    }
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn copy_value(&self) -> Self {
    Self {
      idx: self.idx,
      container_ref: self.container_ref.copy_value(),
    }
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn copy_value(&self) -> Self {
    match self {
      Self::Local(container) => Self::Local(Rc::clone(container)),
      Self::Global { status, container } => Self::Global {
        status: Rc::clone(status),
        container: Rc::clone(container),
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
    use SymContainerImpl::*;

    let res = match (&self.container, &other.container) {
      (General(l), General(r)) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(self.solver, false));
        }
        let mut res = SymBool::from(self.solver, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
      (U8(l), U8(r)) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(self.solver, false));
        }
        let mut res = SymBool::from(self.solver, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
      (U64(l), U64(r)) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(self.solver, false));
        }
        let mut res = SymBool::from(self.solver, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
      (U128(l), U128(r)) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(self.solver, false));
        }
        let mut res = SymBool::from(self.solver, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
      (Bool(l), Bool(r)) => {
        if l.len() != r.len() {
          return Ok(SymBool::from(self.solver, false));
        }
        let mut res = SymBool::from(self.solver, true);
        for (v1, v2) in l.iter().zip(r.iter()) {
          res = res.and(&v1.equals(v2)?);
        }
        res
      }
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
  fn equals(&self, other: &Self) -> VMResult<SymBool<'ctx>> {
    use SymContainerImpl::*;

    let res = match (
      &(*self.container_ref.borrow()).container,
      &(*other.container_ref.borrow()).container,
    ) {
      (General(v1), General(v2)) => v1[self.idx].equals(&v2[other.idx])?,
      (U8(v1), U8(v2)) => v1[self.idx].equals(&v2[other.idx])?,
      (U64(v1), U64(v2)) => v1[self.idx].equals(&v2[other.idx])?,
      (U128(v1), U128(v2)) => v1[self.idx].equals(&v2[other.idx])?,
      (Bool(v1), Bool(v2)) => v1[self.idx].equals(&v2[other.idx])?,

      // Equality between a generic and a specialized container.
      (General(v1), U8(v2)) => v1[self.idx].as_value_ref::<SymU8<'ctx>>()?.equals(&v2[other.idx])?,
      (U8(v1), General(v2)) => v1[self.idx].equals(v2[other.idx].as_value_ref::<SymU8<'ctx>>()?)?,

      (General(v1), U64(v2)) => v1[self.idx].as_value_ref::<SymU64<'ctx>>()?.equals(&v2[other.idx])?,
      (U64(v1), General(v2)) => v1[self.idx].equals(v2[other.idx].as_value_ref::<SymU64<'ctx>>()?)?,

      (General(v1), U128(v2)) => v1[self.idx].as_value_ref::<SymU128<'ctx>>()?.equals(&v2[other.idx])?,
      (U128(v1), General(v2)) => v1[self.idx].equals(v2[other.idx].as_value_ref::<SymU128<'ctx>>()?)?,

      (General(v1), Bool(v2)) => v1[self.idx].as_value_ref::<SymBool<'ctx>>()?.equals(&v2[other.idx])?,
      (Bool(v1), General(v2)) => v1[self.idx].equals(v2[other.idx].as_value_ref::<SymBool<'ctx>>()?)?,

      // All other combinations are illegal.
      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot compare references {:?}, {:?}", self, other)),
        )
      }
    };
    Ok(res)
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
    Ok(SymValue(SymValueImpl::new_container(self.borrow().copy_value())))
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    use SymContainerImpl::*;

    let res = match &(*self.container_ref.borrow()).container {
      General(v) => v[self.idx].copy_value(),
      U8(v) => SymValueImpl::U8(v[self.idx]),
      U64(v) => SymValueImpl::U64(v[self.idx]),
      U128(v) => SymValueImpl::U128(v[self.idx]),
      Bool(v) => SymValueImpl::Bool(v[self.idx]),
    };

    Ok(SymValue(res))
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
  fn write_ref(self, v: SymValue<'ctx>) -> VMResult<()> {
    match v.0 {
      SymValueImpl::Container(r) => {
        *self.borrow_mut() = take_unique_ownership(r)?
        // TODO: can we simply take the Rc?
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
      | SymValueImpl::Invalid
      | SymValueImpl::Container(_) => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
      _ => (),
    }

    match (&mut (*self.container_ref.borrow_mut()).container, &x.0) {
      (SymContainerImpl::General(v), _) => {
        v[self.idx] = x.0;
      }
      (SymContainerImpl::U8(v), SymValueImpl::U8(x)) => v[self.idx] = x.clone(),
      (SymContainerImpl::U64(v), SymValueImpl::U64(x)) => v[self.idx] = x.clone(),
      (SymContainerImpl::U128(v), SymValueImpl::U128(x)) => v[self.idx] = x.clone(),
      (SymContainerImpl::Bool(v), SymValueImpl::Bool(x)) => v[self.idx] = x.clone(),
      _ => {
        return Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
    }
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
  fn borrow_elem(&self, idx: usize) -> VMResult<SymValueImpl<'ctx>> {
    let r = self.borrow();

    if idx >= r.len() {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
          "index out of bounds when borrowing container element: got: {}, len: {}",
          idx,
          r.len()
        )),
      );
    }

    let res = match &(*r).container {
      SymContainerImpl::General(v) => match &v[idx] {
        // TODO: check for the impossible combinations.
        SymValueImpl::Container(container) => {
          let r = match self {
            Self::Local(_) => Self::Local(Rc::clone(container)),
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: Rc::clone(container),
            },
          };
          SymValueImpl::ContainerRef(r)
        }
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
    Ok(SymValue(self.0.borrow_elem(idx)?))
  }
}

impl<'ctx> SymLocals<'ctx> {
  pub fn borrow_loc(&self, idx: usize) -> VMResult<SymValue<'ctx>> {
    // TODO: this is very similar to SharedContainer::borrow_elem. Find a way to
    // reuse that code?

    let r = self.0.borrow();

    if idx >= r.len() {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
          "index out of bounds when borrowing local: got: {}, len: {}",
          idx,
          r.len()
        )),
      );
    }

    match &(*r).container {
      SymContainerImpl::General(v) => match &v[idx] {
        SymValueImpl::Container(r) => Ok(SymValue(SymValueImpl::ContainerRef(
          SymContainerRef::Local(Rc::clone(r)),
        ))),

        SymValueImpl::U8(_)
        | SymValueImpl::U64(_)
        | SymValueImpl::U128(_)
        | SymValueImpl::Bool(_)
        | SymValueImpl::Address(_)
        | SymValueImpl::Signer(_) => Ok(SymValue(SymValueImpl::IndexedRef(SymIndexedRef {
          container_ref: SymContainerRef::Local(Rc::clone(&self.0)),
          idx,
        }))),

        SymValueImpl::ContainerRef(_) | SymValueImpl::Invalid | SymValueImpl::IndexedRef(_) => Err(
          VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message(format!("cannot borrow local {:?}", &v[idx])),
        ),
      },
      v => Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("bad container for locals: {:?}", v)),
      ),
    }
  }
}

/***************************************************************************************
*
* Locals
*
*   Public APIs for Locals to support reading, writing and moving of values.
*
**************************************************************************************/
impl<'ctx> SymLocals<'ctx> {
  pub fn new(solver: &'ctx Solver<'ctx>, n: usize) -> Self {
    Self(Rc::new(RefCell::new(SymContainer {
      solver,
      container: SymContainerImpl::General(
        iter::repeat_with(|| SymValueImpl::Invalid)
          .take(n)
          .collect(),
      ),
    })))
  }

  pub fn copy_loc(&self, idx: usize) -> VMResult<SymValue<'ctx>> {
    let r = self.0.borrow();
    let v = match &(*r).container {
      SymContainerImpl::General(v) => v,
      _ => unreachable!(),
    };

    match v.get(idx) {
      Some(SymValueImpl::Invalid) => Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot copy invalid value at index {}", idx)),
      ),
      Some(v) => Ok(SymValue(v.copy_value())),
      None => Err(
        VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(format!(
          "local index out of bounds: got {}, len: {}",
          idx,
          v.len()
        )),
      ),
    }
  }

  fn swap_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> VMResult<SymValue<'ctx>> {
    let mut r = self.0.borrow_mut();
    let v = match &mut (*r).container {
      SymContainerImpl::General(v) => v,
      _ => unreachable!(),
    };

    match v.get_mut(idx) {
      Some(v) => {
        if let SymValueImpl::Container(r) = v {
          if Rc::strong_count(r) > 1 {
            return Err(
              VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                .with_message("moving container with dangling references".to_string()),
            );
          }
        }
        Ok(SymValue(std::mem::replace(v, x.0)))
      }
      None => Err(
        VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(format!(
          "local index out of bounds: got {}, len: {}",
          idx,
          v.len()
        )),
      ),
    }
  }

  pub fn move_loc(&mut self, idx: usize) -> VMResult<SymValue<'ctx>> {
    match self.swap_loc(idx, SymValue(SymValueImpl::Invalid))? {
      SymValue(SymValueImpl::Invalid) => Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot move invalid value at index {}", idx)),
      ),
      v => Ok(v),
    }
  }

  pub fn store_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> VMResult<()> {
    self.swap_loc(idx, x)?;
    Ok(())
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
  pub fn from_u8(solver: &Solver<'ctx>, value: u8) -> Self {
    SymValue(SymValueImpl::U8(SymU8::from(solver, value)))
  }

  pub fn from_sym_u8(sym: SymU8<'ctx>) -> Self {
    SymValue(SymValueImpl::U8(sym))
  }

  pub fn new_u8(solver: &Solver<'ctx>, prefix: &str) -> Self {
    SymValue(SymValueImpl::U8(SymU8::new(solver, prefix)))
  }

  pub fn from_u64(solver: &Solver<'ctx>, value: u64) -> Self {
    SymValue(SymValueImpl::U64(SymU64::from(solver, value)))
  }

  pub fn from_sym_u64(sym: SymU64<'ctx>) -> Self {
    SymValue(SymValueImpl::U64(sym))
  }

  pub fn new_u64(solver: &Solver<'ctx>, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(SymU64::new(solver, prefix)))
  }

  pub fn from_u128(solver: &Solver<'ctx>, value: u128) -> Self {
    SymValue(SymValueImpl::U128(SymU128::from(solver, value)))
  }

  pub fn from_sym_u128(sym: SymU128<'ctx>) -> Self {
    SymValue(SymValueImpl::U128(sym))
  }

  pub fn new_u128(solver: &Solver<'ctx>, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(SymU128::new(solver, prefix)))
  }

  pub fn from_bool(solver: &Solver<'ctx>, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::from(solver, value)))
  }

  pub fn from_sym_bool(sym: SymBool<'ctx>) -> Self {
    SymValue(SymValueImpl::Bool(sym))
  }

  pub fn new_bool(solver: &Solver<'ctx>, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::new(solver, prefix)))
  }

  pub fn from_address(solver: &'ctx Solver, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(
      solver, address,
    )))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn from_signer(solver: &'ctx Solver, signer: AccountAddress) -> Self {
    SymValue(SymValueImpl::Signer(SymAccountAddress::new(
      solver, signer,
    )))
  }

  pub fn from_sym_signer(signer: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Signer(signer))
  }

  pub fn from_sym_struct(s: SymStruct<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(s.0))
  }

  // TODO: consider whether we want to replace these with fn vector(v: Vec<Value>).
  // pub fn vector_u8(it: impl IntoIterator<Item = u8>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainerImpl::U8(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_u64(it: impl IntoIterator<Item = u64>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainerImpl::U64(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_u128(it: impl IntoIterator<Item = u128>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainerImpl::U128(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_bool(it: impl IntoIterator<Item = bool>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainerImpl::Bool(
  //     it.into_iter().collect(),
  //   )))
  // }

  // pub fn vector_address(it: impl IntoIterator<Item = SymAccountAddress<'ctx>>) -> Self {
  //   Self(SymValueImpl::new_container(SymContainerImpl::General(
  //     it.into_iter().map(SymValueImpl::Address).collect(),
  //   )))
  // }
}

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
pub trait VMValueCast<T> {
  fn cast(self) -> VMResult<T>;
}

macro_rules! impl_vm_value_cast {
  ($ty: ty, $tc: ident) => {
    impl<'ctx> VMValueCast<$ty> for SymValue<'ctx> {
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
impl_vm_value_cast!(SymU8<'ctx>, U8);
impl_vm_value_cast!(SymU64<'ctx>, U64);
impl_vm_value_cast!(SymU128<'ctx>, U128);
impl_vm_value_cast!(SymBool<'ctx>, Bool);
impl_vm_value_cast!(SymAccountAddress<'ctx>, Address);
impl_vm_value_cast!(SymContainerRef<'ctx>, ContainerRef);
impl_vm_value_cast!(SymIndexedRef<'ctx>, IndexedRef);

impl<'ctx> VMValueCast<SymIntegerValue<'ctx>> for SymValue<'ctx> {
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

impl<'ctx> VMValueCast<SymReference<'ctx>> for SymValue<'ctx> {
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

impl<'ctx> VMValueCast<SymContainer<'ctx>> for SymValue<'ctx> {
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
impl<'ctx> VMValueCast<Vec<SymValue<'ctx>>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<Vec<SymValue<'ctx>>> {
    match self.0 {
      SymValueImpl::Container(r) => Ok(match take_unique_ownership(r)?.container {
        SymContainerImpl::General(vs) => vs.into_iter().map(SymValue).collect(),
        SymContainerImpl::U8(vs) => vs.into_iter().map(SymValue::u8).collect(),
        SymContainerImpl::U64(vs) => vs.into_iter().map(SymValue::u64).collect(),
        SymContainerImpl::U128(vs) => vs.into_iter().map(SymValue::u128).collect(),
        SymContainerImpl::Bool(vs) => vs.into_iter().map(SymValue::bool).collect(),
      }),
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to vector of values", v,)),
      ),
    }
  }
}

impl<'ctx> VMValueCast<SymStruct<'ctx>> for SymValue<'ctx> {
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

impl<'ctx> VMValueCast<SymStructRef<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<SymStructRef<'ctx>> {
    Ok(SymStructRef(VMValueCast::cast(self)?))
  }
}

impl<'ctx> VMValueCast<Vec<SymU8<'ctx>>> for SymValue<'ctx> {
  fn cast(self) -> VMResult<Vec<SymU8<'ctx>>> {
    match self.0 {
      SymValueImpl::Container(r) => match take_unique_ownership(r)?.container {
        SymContainerImpl::U8(v) => Ok(v),
        v => Err(
          VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
        ),
      },
      v => Err(
        VMStatus::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
      ),
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn value_as<T>(self) -> VMResult<T>
  where
    Self: VMValueCast<T>,
  {
    VMValueCast::cast(self)
  }
}

impl<'ctx> VMValueCast<SymU8<'ctx>> for SymIntegerValue<'ctx> {
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

impl<'ctx> VMValueCast<SymU64<'ctx>> for SymIntegerValue<'ctx> {
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

impl<'ctx> VMValueCast<SymU128<'ctx>> for SymIntegerValue<'ctx> {
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
    Self: VMValueCast<T>,
  {
    VMValueCast::cast(self)
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
* Vector
*
*   Native function imeplementations of the Vector module.
*
*   TODO: split the code into two parts:
*         1) Internal vector APIs that define & implements the core operations
           (and operations only).
*         2) Native function adapters that the dispatcher can call into. These will
*            check if arguments are valid and deal with gas metering.
*
**************************************************************************************/

// pub mod vector {
//   use super::*;
//   use crate::{loaded_data::runtime_types::Type, natives::function::NativeContext};

//   pub const INDEX_OUT_OF_BOUNDS: u64 = NFE_VECTOR_ERROR_BASE + 1;
//   pub const POP_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 2;
//   pub const DESTROY_NON_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 3;

//   macro_rules! pop_arg_front {
//     ($arguments:ident, $t:ty) => {
//       $arguments.pop_front().unwrap().value_as::<$t>()?
//     };
//   }

//   fn check_elem_layout(ty: &Type, v: &Container) -> VMResult<()> {
//     match (ty, v) {
//       (Type::U8, Container::U8(_))
//       | (Type::U64, Container::U64(_))
//       | (Type::U128, Container::U128(_))
//       | (Type::Bool, Container::Bool(_))
//       | (Type::Address, Container::General(_))
//       | (Type::Signer, Container::General(_))
//       | (Type::Vector(_), Container::General(_))
//       | (Type::Struct(_), Container::General(_)) => Ok(()),
//       (Type::StructInstantiation(_, _), Container::General(_)) => Ok(()),

//       (Type::Reference(_), _) | (Type::MutableReference(_), _) | (Type::TyParam(_), _) => Err(
//         VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//           .with_message(format!("invalid type param for vector: {:?}", ty)),
//       ),

//       (Type::U8, _)
//       | (Type::U64, _)
//       | (Type::U128, _)
//       | (Type::Bool, _)
//       | (Type::Address, _)
//       | (Type::Signer, _)
//       | (Type::Vector(_), _)
//       | (Type::Struct(_), _)
//       | (Type::StructInstantiation(_, _), _) => Err(
//         VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
//           "vector elem layout mismatch, expected {:?}, got {:?}",
//           ty, v
//         )),
//       ),
//     }
//   }

//   pub fn native_empty(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.is_empty());

//     let cost = native_gas(context.cost_table(), NativeCostIndex::EMPTY, 1);

//     let container = match &ty_args[0] {
//       Type::U8 => Container::U8(vec![]),
//       Type::U64 => Container::U64(vec![]),
//       Type::U128 => Container::U128(vec![]),
//       Type::Bool => Container::Bool(vec![]),

//       Type::Address
//       | Type::Signer
//       | Type::Vector(_)
//       | Type::Struct(_)
//       | Type::StructInstantiation(_, _) => Container::General(vec![]),

//       Type::Reference(_) | Type::MutableReference(_) | Type::TyParam(_) => {
//         return Err(
//           VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//             .with_message(format!("invalid type param for vector: {:?}", &ty_args[0])),
//         )
//       }
//     };

//     Ok(NativeResult::ok(
//       cost,
//       vec![Value(SymValueImpl::new_container(container))],
//     ))
//   }

//   pub fn native_length(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 1);

//     let r = pop_arg_front!(args, ContainerRef);

//     let cost = native_gas(context.cost_table(), NativeCostIndex::LENGTH, 1);

//     let v = r.borrow();
//     check_elem_layout(&ty_args[0], &*v)?;
//     let len = match &*v {
//       Container::U8(v) => v.len(),
//       Container::U64(v) => v.len(),
//       Container::U128(v) => v.len(),
//       Container::Bool(v) => v.len(),
//       Container::General(v) => v.len(),
//     };

//     Ok(NativeResult::ok(cost, vec![Value::u64(len as u64)]))
//   }

//   pub fn native_push_back(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 2);

//     let r = pop_arg_front!(args, ContainerRef);
//     let e = args.pop_front().unwrap();

//     let cost = native_gas(
//       context.cost_table(),
//       NativeCostIndex::PUSH_BACK,
//       e.size().get() as usize,
//     );

//     let mut v = r.borrow_mut();
//     check_elem_layout(&ty_args[0], &*v)?;
//     match &mut *v {
//       Container::U8(v) => v.push(e.value_as()?),
//       Container::U64(v) => v.push(e.value_as()?),
//       Container::U128(v) => v.push(e.value_as()?),
//       Container::Bool(v) => v.push(e.value_as()?),
//       Container::General(v) => v.push(e.0),
//     }

//     Ok(NativeResult::ok(cost, vec![]))
//   }

//   pub fn native_borrow(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 2);

//     let r = pop_arg_front!(args, ContainerRef);
//     let idx = pop_arg_front!(args, u64) as usize;

//     let cost = native_gas(context.cost_table(), NativeCostIndex::BORROW, 1);

//     let v = r.borrow();
//     check_elem_layout(&ty_args[0], &*v)?;
//     if idx >= v.len() {
//       return Ok(NativeResult::err(
//         cost,
//         VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(INDEX_OUT_OF_BOUNDS),
//       ));
//     }
//     let v = Value(r.borrow_elem(idx)?);

//     Ok(NativeResult::ok(cost, vec![v]))
//   }

//   pub fn native_pop(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 1);

//     let r = pop_arg_front!(args, ContainerRef);

//     let cost = native_gas(context.cost_table(), NativeCostIndex::POP_BACK, 1);

//     let mut v = r.borrow_mut();
//     check_elem_layout(&ty_args[0], &*v)?;

//     macro_rules! err_pop_empty_vec {
//       () => {
//         return Ok(NativeResult::err(
//           cost,
//           VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(POP_EMPTY_VEC),
//         ));
//       };
//     }

//     let res = match &mut *v {
//       Container::U8(v) => match v.pop() {
//         Some(x) => Value::u8(x),
//         None => err_pop_empty_vec!(),
//       },
//       Container::U64(v) => match v.pop() {
//         Some(x) => Value::u64(x),
//         None => err_pop_empty_vec!(),
//       },
//       Container::U128(v) => match v.pop() {
//         Some(x) => Value::u128(x),
//         None => err_pop_empty_vec!(),
//       },
//       Container::Bool(v) => match v.pop() {
//         Some(x) => Value::bool(x),
//         None => err_pop_empty_vec!(),
//       },

//       Container::General(v) => match v.pop() {
//         Some(x) => Value(x),
//         None => err_pop_empty_vec!(),
//       },
//     };

//     Ok(NativeResult::ok(cost, vec![res]))
//   }

//   pub fn native_destroy_empty(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 1);
//     let v = args.pop_front().unwrap().value_as::<Container>()?;

//     let cost = native_gas(context.cost_table(), NativeCostIndex::DESTROY_EMPTY, 1);

//     check_elem_layout(&ty_args[0], &v)?;

//     let is_empty = match &v {
//       Container::U8(v) => v.is_empty(),
//       Container::U64(v) => v.is_empty(),
//       Container::U128(v) => v.is_empty(),
//       Container::Bool(v) => v.is_empty(),

//       Container::General(v) => v.is_empty(),
//     };

//     if is_empty {
//       Ok(NativeResult::ok(cost, vec![]))
//     } else {
//       Ok(NativeResult::err(
//         cost,
//         VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(DESTROY_NON_EMPTY_VEC),
//       ))
//     }
//   }

//   pub fn native_swap(
//     context: &impl NativeContext,
//     ty_args: Vec<Type>,
//     mut args: VecDeque<Value>,
//   ) -> VMResult<NativeResult> {
//     debug_assert!(ty_args.len() == 1);
//     debug_assert!(args.len() == 3);
//     let r = pop_arg_front!(args, ContainerRef);
//     let idx1 = pop_arg_front!(args, u64) as usize;
//     let idx2 = pop_arg_front!(args, u64) as usize;

//     let cost = native_gas(context.cost_table(), NativeCostIndex::SWAP, 1);

//     let mut v = r.borrow_mut();
//     check_elem_layout(&ty_args[0], &*v)?;

//     macro_rules! swap {
//       ($v: ident) => {{
//         if idx1 >= $v.len() || idx2 >= $v.len() {
//           return Ok(NativeResult::err(
//             cost,
//             VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(INDEX_OUT_OF_BOUNDS),
//           ));
//         }
//         $v.swap(idx1, idx2);
//       }};
//     }

//     match &mut *v {
//       Container::U8(v) => swap!(v),
//       Container::U64(v) => swap!(v),
//       Container::U128(v) => swap!(v),
//       Container::Bool(v) => swap!(v),
//       Container::General(v) => swap!(v),
//     }

//     Ok(NativeResult::ok(cost, vec![]))
//   }
// }

/***************************************************************************************
*
* Gas
*
*   Abstract memory sizes of the VM values.
*
**************************************************************************************/

// impl<'ctx> SymContainer<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     match self {
//       Self::General(v) => v
//         .iter()
//         .fold(STRUCT_SIZE, |acc, v| acc.map2(v.size(), Add::add)),
//       Self::U8(v) => AbstractMemorySize::new((v.len() * size_of::<u8>()) as u64),
//       Self::U64(v) => AbstractMemorySize::new((v.len() * size_of::<u64>()) as u64),
//       Self::U128(v) => AbstractMemorySize::new((v.len() * size_of::<u128>()) as u64),
//       Self::Bool(v) => AbstractMemorySize::new((v.len() * size_of::<bool>()) as u64),
//     }
//   }
// }

// impl<'ctx> SymContainerRef<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     words_in(REFERENCE_SIZE)
//   }
// }

// impl<'ctx> SymIndexedRef<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     words_in(REFERENCE_SIZE)
//   }
// }

// impl<'ctx> SymValueImpl<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     use SymValueImpl::*;

//     match self {
//       Invalid | U8(_) | U64(_) | U128(_) | Bool(_) => CONST_SIZE,
//       Address(_) | Signer(_) => AbstractMemorySize::new(SymAccountAddress::LENGTH as u64),
//       ContainerRef(r) => r.size(),
//       IndexedRef(r) => r.size(),
//       // TODO: in case the borrow fails the VM will panic.
//       Container(r) => r.borrow().size(),
//     }
//   }
// }

// impl<'ctx> SymStruct<'ctx> {
//   pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     self.0.size()
//   }
// }

// impl<'ctx> SymValue<'ctx> {
//   pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     self.0.size()
//   }
// }

// impl<'ctx> SymReferenceImpl<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     match self {
//       Self::ContainerRef(r) => r.size(),
//       Self::IndexedRef(r) => r.size(),
//     }
//   }
// }

// impl<'ctx> SymReference<'ctx> {
//   pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     self.0.size()
//   }
// }

// impl<'ctx> SymGlobalValue<'ctx> {
//   pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     // TODO: should it be self.container.borrow().size()
//     words_in(REFERENCE_SIZE)
//   }
// }

/***************************************************************************************
*
* Struct Operations
*
*   Public APIs for Struct.
*
**************************************************************************************/
impl<'ctx> SymStruct<'ctx> {
  pub fn pack<I: IntoIterator<Item = SymValue<'ctx>>>(solver: &'ctx Solver<'ctx>, vals: I) -> Self {
    Self(SymContainer {
      solver,
      container: SymContainerImpl::General(
        vals.into_iter().map(|v| v.0).collect(),
      ),
    })
  }

  pub fn unpack(self) -> VMResult<impl Iterator<Item = SymValue<'ctx>>> {
    match self.0.container {
      SymContainerImpl::General(v) => Ok(v.into_iter().map(SymValue)),
      SymContainerImpl::U8(_)
      | SymContainerImpl::U64(_)
      | SymContainerImpl::U128(_)
      | SymContainerImpl::Bool(_) => Err(
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
    Ok(SymValue(SymValueImpl::ContainerRef(SymContainerRef::Global {
      status: Rc::clone(&self.status),
      container: Rc::clone(&self.container),
    })))
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
      Self::Address(addr) => write!(f, "SymAddress({})", addr.short_str()),
      Self::Signer(addr) => write!(f, "SymSigner({})", addr.short_str()),

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
      Self::Local(r) => write!(f, "({}, {})", Rc::strong_count(r), &*r.borrow()),
      Self::Global { status, container } => write!(
        f,
        "({:?}, {}, {})",
        &*status.borrow(),
        Rc::strong_count(container),
        &*container.borrow()
      ),
    }
  }
}

impl<'ctx> Display for SymIndexedRef<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{}<{}>", self.container_ref, self.idx)
  }
}

impl<'ctx> Display for SymContainer<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self.container {
      Self::General(v) => display_list_of_items(v, f),
      Self::U8(v) => display_list_of_items(v, f),
      Self::U64(v) => display_list_of_items(v, f),
      Self::U128(v) => display_list_of_items(v, f),
      Self::Bool(v) => display_list_of_items(v, f),
    }
  }
}

impl<'ctx> Display for SymValue<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    Display::fmt(&self.0, f)
  }
}

impl<'ctx> Display for SymLocals<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    // TODO: this could panic.
    match &(*self.0.borrow()).container {
      SymContainerImpl::General(v) => write!(
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

//     Ok(NativeResult::ok(ZERO_GAS_UNITS, vec![]))
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

//     Ok(NativeResult::ok(ZERO_GAS_UNITS, vec![]))
//   }
// }
