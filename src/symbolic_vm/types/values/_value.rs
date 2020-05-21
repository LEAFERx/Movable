// This file is a symbolic version of libra/language/vm/vm-runtime/vm-runtime-types/value/value-impl.rs
// Currently gas system is not implemented

use libra_types::{
  account_address::AccountAddress,
  byte_array::ByteArray,
  // language_storage::TypeTag,
  vm_error::{
    // sub_status::NFE_VECTOR_ERROR_BASE,
    StatusCode,
    VMStatus,
  },
};
use std::{
  cell::{Ref, RefCell, RefMut},
  // collections::VecDeque,
  fmt::{self, Debug, Display},
  iter,
  // mem::size_of,
  // ops::Add,
  rc::Rc,
};
use vm::{
  errors::*,
  file_format::SignatureToken,
  // gas_schedule::{
  //   words_in, AbstractMemorySize, CostTable, GasAlgebra, GasCarrier, NativeCostIndex, CONST_SIZE,
  //   REFERENCE_SIZE, STRUCT_SIZE,
  // },
};
// use vm_runtime_types::{
//   loaded_data::{struct_def::StructDef, types::Type},
//   native_functions::dispatch::{native_gas, NativeResult},
//   native_structs::def::{NativeStructTag, NativeStructType},
// };

use z3::ast::Dynamic;

use crate::{
  engine::solver::Solver,
  symbolic_vm::types::{
    account_address::SymAccountAddress,
    byte_array::SymByteArray,
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
  ByteArray(SymByteArray<'ctx>),

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

/// A SymContainerRef<'ctx> is a direct reference to a container, which could live either in the frame
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

/// A Move value -- a wrapper around `SymValueImpl` which can be created only through valid
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
      (SignatureToken::ByteArray, SymValueImpl::ByteArray(_)) => true,
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
impl_vm_value_ref!(SymByteArray<'ctx>, ByteArray);

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

      U8(x) => U8(x.clone()),
      U64(x) => U64(x.clone()),
      U128(x) => U128(x.clone()),
      Bool(x) => Bool(x.clone()),
      Address(x) => Address(x.clone()),
      ByteArray(x) => ByteArray(x.clone()),

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
      (ByteArray(l), ByteArray(r)) => l.equals(r)?,
      (Address(l), Address(r)) => l.equals(r)?,

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
    Ok(SymValue(SymValueImpl::new_container(
      self.borrow().copy_value(),
    )))
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn read_ref(self) -> VMResult<SymValue<'ctx>> {
    use SymContainerImpl::*;

    let res = match &(*self.container_ref.borrow()).container {
      General(v) => v[self.idx].copy_value(),
      U8(v) => SymValueImpl::U8(v[self.idx].clone()),
      U64(v) => SymValueImpl::U64(v[self.idx].clone()),
      U128(v) => SymValueImpl::U128(v[self.idx].clone()),
      Bool(v) => SymValueImpl::Bool(v[self.idx].clone()),
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
    // TODO: this is very similar to SharedSymContainerImpl::borrow_elem. Find a way to
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
        | SymValueImpl::ByteArray(_) => Ok(SymValue(SymValueImpl::IndexedRef(SymIndexedRef {
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

  pub fn from_byte_array(_solver: &'ctx Solver, _bytearray: ByteArray) -> Self {
    unimplemented!()
  }

  pub fn from_sym_byte_array(bytearray: SymByteArray<'ctx>) -> Self {
    SymValue(SymValueImpl::ByteArray(bytearray))
  }

  pub fn new_byte_array(_solver: &'ctx Solver, _prefix: &str) -> Self {
    unimplemented!()
  }

  pub fn from_address(solver: &'ctx Solver, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(
      solver, address,
    )))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn from_sym_struct(s: SymStruct<'ctx>) -> Self {
    SymValue(SymValueImpl::new_container(s.0))
  }
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
pub trait VMSymValueCast<T> {
  fn cast(self) -> VMResult<T>;
}

macro_rules! impl_vm_value_cast {
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
impl_vm_value_cast!(SymU8<'ctx>, U8);
impl_vm_value_cast!(SymU64<'ctx>, U64);
impl_vm_value_cast!(SymU128<'ctx>, U128);
impl_vm_value_cast!(SymBool<'ctx>, Bool);
impl_vm_value_cast!(SymAccountAddress<'ctx>, Address);
impl_vm_value_cast!(SymByteArray<'ctx>, ByteArray);
impl_vm_value_cast!(SymContainerRef<'ctx>, ContainerRef);
impl_vm_value_cast!(SymIndexedRef<'ctx>, IndexedRef);

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

  pub fn into_value(self) -> SymValue<'ctx> {
    use SymIntegerValue::*;

    match self {
      U8(x) => SymValue::from_sym_u8(x),
      U64(x) => SymValue::from_sym_u64(x),
      U128(x) => SymValue::from_sym_u128(x),
    }
  }
}

// Do not implement From<SymIntegerValue<'ctx> for SymUxx<'ctx>
// Use explicit cast_uxx()

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

//   pub const INDEX_OUT_OF_BOUNDS: u64 = NFE_VECTOR_ERROR_BASE + 1;
//   pub const POP_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 2;
//   pub const DESTROY_NON_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 3;

//   macro_rules! ensure_len {
//     ($v: expr, $expected_len: expr, $type: expr, $fn: expr) => {{
//       let actual_len = $v.len();
//       let expected_len = $expected_len;
//       if actual_len != expected_len {
//         let msg = format!(
//           "wrong number of {} for {} expected {} found {}",
//           ($type),
//           ($fn),
//           expected_len,
//           actual_len,
//         );
//         return Err(VMStatus::new(StatusCode::UNREACHABLE).with_message(msg));
//       }
//     }};
//   }

//   macro_rules! pop_arg_front {
//     ($arguments:ident, $t:ty) => {
//       $arguments.pop_front().unwrap().value_as::<$t>()?
//     };
//   }

//   macro_rules! err_vector_elem_ty_mismatch {
//     () => {{
//       return Err(
//         VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//           .with_message("vector elem type mismatch".to_string()),
//       );
//     }};
//   }

//   pub fn native_empty(
//     ty_args: Vec<TypeTag>,
//     args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "empty");
//     ensure_len!(args, 0, "arguments", "empty");

//     let cost = native_gas(cost_table, NativeCostIndex::EMPTY, 1);
//     let container = match &ty_args[0] {
//       TypeTag::U8 => SymContainerImpl::U8(vec![]),
//       TypeTag::U64 => SymContainerImpl::U64(vec![]),
//       TypeTag::U128 => SymContainerImpl::U128(vec![]),
//       TypeTag::Bool => SymContainerImpl::Bool(vec![]),

//       _ => SymContainerImpl::General(vec![]),
//     };

//     Ok(NativeResult::ok(
//       cost,
//       vec![Value(SymValueImpl::new_container(container))],
//     ))
//   }

//   pub fn native_length(
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "length");
//     ensure_len!(args, 1, "arguments", "length");

//     let cost = native_gas(cost_table, NativeCostIndex::LENGTH, 1);
//     let r = pop_arg_front!(args, SymContainerRef<'ctx>);
//     let v = r.borrow();

//     let len = match (&ty_args[0], &*v) {
//       (TypeTag::U8, SymContainerImpl::U8(v)) => v.len(),
//       (TypeTag::U64, SymContainerImpl::U64(v)) => v.len(),
//       (TypeTag::U128, SymContainerImpl::U128(v)) => v.len(),
//       (TypeTag::Bool, SymContainerImpl::Bool(v)) => v.len(),

//       (TypeTag::Struct(_), SymContainerImpl::General(v))
//       | (TypeTag::ByteArray, SymContainerImpl::General(v))
//       | (TypeTag::Address, SymContainerImpl::General(v)) => v.len(),

//       _ => err_vector_elem_ty_mismatch!(),
//     };

//     Ok(NativeResult::ok(cost, vec![Value::u64(len as u64)]))
//   }

//   pub fn native_push_back(
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "push back");
//     ensure_len!(args, 2, "arguments", "push back");

//     let r = pop_arg_front!(args, SymContainerRef<'ctx>);
//     let mut v = r.borrow_mut();
//     let e = args.pop_front().unwrap();

//     let cost = cost_table
//       .native_cost(NativeCostIndex::PUSH_BACK)
//       .total()
//       .mul(e.size());

//     match (&ty_args[0], &mut *v) {
//       (TypeTag::U8, SymContainerImpl::U8(v)) => v.push(e.value_as()?),
//       (TypeTag::U64, SymContainerImpl::U64(v)) => v.push(e.value_as()?),
//       (TypeTag::U128, SymContainerImpl::U128(v)) => v.push(e.value_as()?),
//       (TypeTag::Bool, SymContainerImpl::Bool(v)) => v.push(e.value_as()?),

//       (TypeTag::Struct(_), SymContainerImpl::General(v))
//       | (TypeTag::ByteArray, SymContainerImpl::General(v))
//       | (TypeTag::Address, SymContainerImpl::General(v)) => v.push(e.0),

//       _ => err_vector_elem_ty_mismatch!(),
//     }

//     Ok(NativeResult::ok(cost, vec![]))
//   }

//   pub fn native_borrow(
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "borrow");
//     ensure_len!(args, 2, "arguments", "borrow");

//     let cost = native_gas(cost_table, NativeCostIndex::BORROW, 1);
//     let r = pop_arg_front!(args, SymContainerRef<'ctx>);
//     let v = r.borrow();
//     let idx = pop_arg_front!(args, u64) as usize;

//     // TODO: check if the type tag matches the real type?
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
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "pop");
//     ensure_len!(args, 1, "arguments", "pop");

//     let cost = native_gas(cost_table, NativeCostIndex::POP_BACK, 1);
//     let r = pop_arg_front!(args, SymContainerRef<'ctx>);
//     let mut v = r.borrow_mut();

//     macro_rules! err_pop_empty_vec {
//       () => {
//         return Ok(NativeResult::err(
//           cost,
//           VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(POP_EMPTY_VEC),
//         ));
//       };
//     }

//     let res = match (&ty_args[0], &mut *v) {
//       (TypeTag::U8, SymContainerImpl::U8(v)) => match v.pop() {
//         Some(x) => Value::u8(x),
//         None => err_pop_empty_vec!(),
//       },
//       (TypeTag::U64, SymContainerImpl::U64(v)) => match v.pop() {
//         Some(x) => Value::u64(x),
//         None => err_pop_empty_vec!(),
//       },
//       (TypeTag::U128, SymContainerImpl::U128(v)) => match v.pop() {
//         Some(x) => Value::u128(x),
//         None => err_pop_empty_vec!(),
//       },
//       (TypeTag::Bool, SymContainerImpl::Bool(v)) => match v.pop() {
//         Some(x) => Value::bool(x),
//         None => err_pop_empty_vec!(),
//       },

//       (TypeTag::Struct(_), SymContainerImpl::General(v))
//       | (TypeTag::ByteArray, SymContainerImpl::General(v))
//       | (TypeTag::Address, SymContainerImpl::General(v)) => match v.pop() {
//         Some(x) => Value(x),
//         None => err_pop_empty_vec!(),
//       },

//       _ => err_vector_elem_ty_mismatch!(),
//     };

//     Ok(NativeResult::ok(cost, vec![res]))
//   }

//   pub fn native_destroy_empty(
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "destroy empty");
//     ensure_len!(args, 1, "arguments", "destroy empty");

//     let cost = native_gas(cost_table, NativeCostIndex::DESTROY_EMPTY, 1);
//     let v = args.pop_front().unwrap().value_as::<SymContainer<'ctx>>()?;

//     let is_empty = match (&ty_args[0], &v) {
//       (TypeTag::U8, SymContainerImpl::U8(v)) => v.is_empty(),
//       (TypeTag::U64, SymContainerImpl::U64(v)) => v.is_empty(),
//       (TypeTag::U128, SymContainerImpl::U128(v)) => v.is_empty(),
//       (TypeTag::Bool, SymContainerImpl::Bool(v)) => v.is_empty(),

//       (TypeTag::Struct(_), SymContainerImpl::General(v))
//       | (TypeTag::ByteArray, SymContainerImpl::General(v))
//       | (TypeTag::Address, SymContainerImpl::General(v)) => v.is_empty(),

//       _ => err_vector_elem_ty_mismatch!(),
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
//     ty_args: Vec<TypeTag>,
//     mut args: VecDeque<Value>,
//     cost_table: &CostTable,
//   ) -> VMResult<NativeResult> {
//     ensure_len!(ty_args, 1, "type arguments", "swap");
//     ensure_len!(args, 3, "arguments", "swap");

//     let cost = native_gas(cost_table, NativeCostIndex::SWAP, 1);
//     let r = pop_arg_front!(args, SymContainerRef<'ctx>);
//     let mut v = r.borrow_mut();
//     let idx1 = pop_arg_front!(args, u64) as usize;
//     let idx2 = pop_arg_front!(args, u64) as usize;

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

//     match (&ty_args[0], &mut *v) {
//       (TypeTag::U64, SymContainerImpl::U64(v)) => swap!(v),
//       (TypeTag::Bool, SymContainerImpl::Bool(v)) => swap!(v),
//       (TypeTag::Struct(_), SymContainerImpl::General(v))
//       | (TypeTag::Address, SymContainerImpl::General(v))
//       | (TypeTag::ByteArray, SymContainerImpl::General(v)) => swap!(v),
//       _ => err_vector_elem_ty_mismatch!(),
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
//     use SymContainerImpl::*;

//     match self.container {
//       General(v) => v
//         .iter()
//         .fold(*STRUCT_SIZE, |acc, v| acc.map2(v.size(), Add::add)),
//       U8(v) => AbstractMemorySize::new((v.len() * size_of::<u8>()) as u64),
//       U64(v) => AbstractMemorySize::new((v.len() * size_of::<u64>()) as u64),
//       U128(v) => AbstractMemorySize::new((v.len() * size_of::<u128>()) as u64),
//       Bool(v) => AbstractMemorySize::new((v.len() * size_of::<bool>()) as u64),
//     }
//   }
// }

// impl<'ctx> SymContainerRef<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     words_in(*REFERENCE_SIZE)
//   }
// }

// impl<'ctx> SymIndexedRef<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     words_in(*REFERENCE_SIZE)
//   }
// }

// impl<'ctx> SymValueImpl<'ctx> {
//   fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     use SymValueImpl::*;

//     match self {
//       Invalid | U8(_) | U64(_) | U128(_) | Bool(_) => *CONST_SIZE,
//       Address(_) => AbstractMemorySize::new(ADDRESS_LENGTH as u64),
//       ByteArray(key) => AbstractMemorySize::new(key.len() as u64),
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
//     words_in(*REFERENCE_SIZE)
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
    Ok(SymValue(SymValueImpl::ContainerRef(
      SymContainerRef::Global {
        status: Rc::clone(&self.status),
        container: Rc::clone(&self.container),
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

      Self::U8(x) => write!(f, "U8({})", x),
      Self::U64(x) => write!(f, "U64({})", x),
      Self::U128(x) => write!(f, "U128({})", x),
      Self::Bool(x) => write!(f, "{}", x),
      Self::Address(addr) => write!(f, "Address({})", addr.short_str()),
      Self::ByteArray(x) => write!(f, "ByteArray({})", x),

      Self::Container(r) => write!(f, "Container({})", &*r.borrow()),

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
    use SymContainerImpl::*;

    match &self.container {
      General(v) => display_list_of_items(v, f),
      U8(v) => display_list_of_items(v, f),
      U64(v) => display_list_of_items(v, f),
      U128(v) => display_list_of_items(v, f),
      Bool(v) => display_list_of_items(v, f),
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

// /***************************************************************************************
// *
// * Serialization & Deserialization
// *
// *   LCS implementation for VM values. Note although values are represented as Rust
// *   enums that carry type info in the tags, we should NOT rely on them for
// *   serialization:
// *     1) Depending on the specific internal representation, it may be impossible to
// *        reconstruct the layout from a value. For example, one cannot tell if a general
// *        container is a struct or a value.
// *     2) Even if 1) is not a problem at a certain time, we may change to a different
// *        internal representation that breaks the 1-1 mapping. Extremely speaking, if
// *        we switch to untagged unions one day, none of the type info will be carried
// *        by the value.
// *
// *   Therefore the appropriate & robust way to implement serialization & deserialization
// *   is to involve an explicit representation of the type layout.
// *
// **************************************************************************************/
// use serde::{
//   de::Error as DeError,
//   ser::{Error as SerError, SerializeSeq, SerializeTuple},
//   Deserialize,
// };

// impl<'ctx> SymValue<'ctx> {
//   pub fn simple_deserialize(blob: &[u8], layout: Type) -> VMResult<SymValue<'ctx>> {
//       lcs::from_bytes_seed(&layout, blob)
//           .map_err(|e| VMStatus::new(StatusCode::INVALID_DATA).with_message(e.to_string()))
//   }

//   pub fn simple_serialize(&self, layout: &Type) -> Option<Vec<u8>> {
//       lcs::to_bytes(&AnnotatedValue {
//           layout,
//           val: &self.0,
//       })
//       .ok()
//   }
// }

// impl Struct {
//   pub fn simple_serialize(&self, layout: &StructDef) -> Option<Vec<u8>> {
//       lcs::to_bytes(&AnnotatedValue {
//           layout,
//           val: &self.0,
//       })
//       .ok()
//   }
// }

// struct AnnotatedValue<'a, 'b, T1, T2> {
//   layout: &'a T1,
//   val: &'b T2,
// }

// impl<'a, 'b> serde::Serialize for AnnotatedValue<'a, 'b, Type, SymValueImpl> {
//   fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
//       match (self.layout, self.val) {
//           (Type::U8, SymValueImpl::U8(x)) => serializer.serialize_u8(*x),
//           (Type::U64, SymValueImpl::U64(x)) => serializer.serialize_u64(*x),
//           (Type::U128, SymValueImpl::U128(x)) => serializer.serialize_u128(*x),
//           (Type::Bool, SymValueImpl::Bool(x)) => serializer.serialize_bool(*x),
//           (Type::Address, SymValueImpl::Address(x)) => x.serialize(serializer),
//           (Type::ByteArray, SymValueImpl::ByteArray(x)) => x.serialize(serializer),

//           (Type::Struct(layout), SymValueImpl::Container(r)) => {
//               let r = r.borrow();
//               (AnnotatedValue { layout, val: &*r }).serialize(serializer)
//           }

//           (layout, val) => Err(S::Error::custom(
//               VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//                   .with_message(format!("cannot serialize value {:?} as {:?}", val, layout)),
//           )),
//       }
//   }
// }

// impl<'a, 'b> serde::Serialize for AnnotatedValue<'a, 'b, StructDef, SymContainer<'ctx>> {
//   fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
//       macro_rules! serialize_vec {
//           ($tc: ident, $actuals: expr, $v: expr) => {{
//               TODO: This can cause a panic. Clean it up when we promote Vector to a primitive type.
//               let layout = &$actuals[0];
//               match layout {
//                   Type::$tc => (),
//                   _ => {
//                       return Err(S::Error::custom(
//                           VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//                               .with_message(
//                                   "cannot serialize vector -- element type mismatch".to_string(),
//                               ),
//                       ))
//                   }
//               }
//               let mut t = serializer.serialize_seq(Some($v.len()))?;
//               for val in $v {
//                   t.serialize_element(val)?;
//               }
//               t.end()
//           }};
//       }

//       match (self.layout, self.val) {
//           (StructDef::Struct(inner), SymContainerImpl::General(v)) => {
//               if inner.field_definitions().len() != v.len() {
//                   return Err(S::Error::custom(
//                       VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(
//                           format!(
//                               "cannot serialize struct value {:?} as {:?} -- number of fields mismatch",
//                               self.val, self.layout
//                           ),
//                       ),
//                   ));
//               }
//               let mut t = serializer.serialize_tuple(v.len())?;
//               for (layout, val) in inner.field_definitions().iter().zip(v.iter()) {
//                   t.serialize_element(&AnnotatedValue { layout, val })?;
//               }
//               t.end()
//           }

//           (
//               StructDef::Native(NativeStructType {
//                   tag: NativeStructTag::Vector,
//                   type_actuals,
//               }),
//               SymContainerImpl::General(v),
//           ) => {
//               TODO: This can cause a panic. Clean it up when we promote Vector to a primitive type.
//               let layout = &type_actuals[0];
//               let mut t = serializer.serialize_seq(Some(v.len()))?;
//               for val in v {
//                   t.serialize_element(&AnnotatedValue { layout, val })?;
//               }
//               t.end()
//           }

//           (
//               StructDef::Native(NativeStructType {
//                   tag: NativeStructTag::Vector,
//                   type_actuals,
//               }),
//               SymContainerImpl::U8(v),
//           ) => serialize_vec!(U8, type_actuals, v),

//           (
//               StructDef::Native(NativeStructType {
//                   tag: NativeStructTag::Vector,
//                   type_actuals,
//               }),
//               SymContainerImpl::U64(v),
//           ) => serialize_vec!(U64, type_actuals, v),

//           (
//               StructDef::Native(NativeStructType {
//                   tag: NativeStructTag::Vector,
//                   type_actuals,
//               }),
//               SymContainerImpl::U128(v),
//           ) => serialize_vec!(U128, type_actuals, v),

//           (
//               StructDef::Native(NativeStructType {
//                   tag: NativeStructTag::Vector,
//                   type_actuals,
//               }),
//               SymContainerImpl::Bool(v),
//           ) => serialize_vec!(Bool, type_actuals, v),

//           (val, layout) => Err(S::Error::custom(
//               VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
//                   "cannot serialize container value {:?} as {:?}",
//                   val, layout
//               )),
//           )),
//       }
//   }
// }

// impl<'d> serde::de::DeserializeSeed<'d> for &Type {
//   type Value = Value;

//   fn deserialize<D: serde::de::Deserializer<'d>>(
//       self,
//       deserializer: D,
//   ) -> Result<Self::Value, D::Error> {
//       match self {
//           Type::Bool => bool::deserialize(deserializer).map(Value::bool),
//           Type::U8 => u8::deserialize(deserializer).map(Value::u8),
//           Type::U64 => u64::deserialize(deserializer).map(Value::u64),
//           Type::U128 => u128::deserialize(deserializer).map(Value::u128),
//           Type::ByteArray => ByteArray::deserialize(deserializer).map(Value::byte_array),
//           Type::Address => AccountAddress::deserialize(deserializer).map(Value::address),

//           Type::Struct(layout) => layout.deserialize(deserializer),

//           Type::Reference(_) | Type::MutableReference(_) | Type::TypeVariable(_) => {
//               Err(D::Error::custom(
//                   VMStatus::new(StatusCode::INVALID_DATA)
//                       .with_message(format!("Value type {:?} not possible", self)),
//               ))
//           }
//       }
//   }
// }

// impl<'d> serde::de::DeserializeSeed<'d> for &StructDef {
//   type Value = Value;

//   fn deserialize<D: serde::de::Deserializer<'d>>(
//       self,
//       deserializer: D,
//   ) -> Result<Self::Value, D::Error> {
//       match self {
//           StructDef::Struct(inner) => {
//               struct StructVisitor<'a>(&'a [Type]);
//               impl<'d, 'a> serde::de::Visitor<'d> for StructVisitor<'a> {
//                   type Value = Struct;

//                   fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
//                       formatter.write_str("Struct")
//                   }

//                   fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
//                   where
//                       A: serde::de::SeqAccess<'d>,
//                   {
//                       let mut val = Vec::new();

//                       for (i, field_type) in self.0.iter().enumerate() {
//                           if let Some(elem) = seq.next_element_seed(field_type)? {
//                               val.push(elem)
//                           } else {
//                               return Err(A::Error::invalid_length(i, &self));
//                           }
//                       }
//                       Ok(Struct::pack(val))
//                   }
//               }

//               let field_layouts = inner.field_definitions();
//               Ok(Value::struct_(deserializer.deserialize_tuple(
//                   field_layouts.len(),
//                   StructVisitor(field_layouts),
//               )?))
//           }
//           StructDef::Native(NativeStructType {
//               tag: NativeStructTag::Vector,
//               type_actuals,
//           }) => {
//               struct GeneralVectorVisitor<'a>(&'a Type);
//               impl<'d, 'a> serde::de::Visitor<'d> for GeneralVectorVisitor<'a> {
//                   type Value = SymContainer<'ctx>;

//                   fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
//                       formatter.write_str("Vector")
//                   }

//                   fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
//                   where
//                       A: serde::de::SeqAccess<'d>,
//                   {
//                       let mut vals = Vec::new();
//                       while let Some(elem) = seq.next_element_seed(self.0)? {
//                           vals.push(elem.0)
//                       }
//                       Ok(SymContainerImpl::General(vals))
//                   }
//               }

//               macro_rules! deserialize_specialized_vec {
//                   ($tc: ident, $tc2: ident, $ty: ident) => {{
//                       struct $tc;
//                       impl<'d> serde::de::Visitor<'d> for $tc {
//                           type Value = Vec<$ty>;

//                           fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
//                               formatter.write_str(stringify!($ty))
//                           }

//                           fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
//                           where
//                               A: serde::de::SeqAccess<'d>,
//                           {
//                               let mut vals = Vec::new();
//                               while let Some(elem) = seq.next_element::<$ty>()? {
//                                   vals.push(elem)
//                               }
//                               Ok(vals)
//                           }
//                       }
//                       Ok(SymValue(SymValueImpl::Container<'ctx>(Rc::new(RefCell::new(
//                           SymContainerImpl::$tc2(deserializer.deserialize_seq($tc)?),
//                       )))))
//                   }};
//               }

//               TODO: This can cause a panic. Clean it up when we promote Vector to a primitive type.
//               match &type_actuals[0] {
//                   Type::U8 => deserialize_specialized_vec!(U8VectorVisitor, U8, u8),
//                   Type::U64 => deserialize_specialized_vec!(U64VectorVisitor, U64, u64),
//                   Type::U128 => deserialize_specialized_vec!(U128VectorVisitor, U128, u128),
//                   Type::Bool => deserialize_specialized_vec!(BoolVectorVisitor, Bool, bool),
//                   layout => Ok(SymValue(SymValueImpl::Container<'ctx>(Rc::new(RefCell::new(
//                       deserializer.deserialize_seq(GeneralVectorVisitor(layout))?,
//                   ))))),
//               }
//           }
//       }
//   }
// }

// /***************************************************************************************
// *
// * Prop Testing
// *
// *   Random generation of values that fit into a given layout.
// *
// **************************************************************************************/
// #[cfg(feature = "fuzzing")]
// pub mod prop {
//   use super::*;
//   use proptest::{collection::vec, prelude::*};

//   pub fn value_strategy_with_layout(layout: &Type) -> impl Strategy<Value = Value> {
//       match layout {
//           Type::U8 => any::<u8>().prop_map(Value::u8).boxed(),
//           Type::U64 => any::<u64>().prop_map(Value::u64).boxed(),
//           Type::U128 => any::<u128>().prop_map(Value::u128).boxed(),
//           Type::Bool => any::<bool>().prop_map(Value::bool).boxed(),
//           Type::Address => any::<AccountAddress>().prop_map(Value::address).boxed(),
//           Type::ByteArray => any::<ByteArray>().prop_map(Value::byte_array).boxed(),

//           Type::Struct(StructDef::Native(NativeStructType {
//               tag: NativeStructTag::Vector,
//               type_actuals,
//           })) => match &type_actuals[0] {
//               Type::U8 => vec(any::<u8>(), 0..10)
//                   .prop_map(|vals| Value(SymValueImpl::new_container(SymContainerImpl::U8(vals))))
//                   .boxed(),
//               Type::U64 => vec(any::<u64>(), 0..10)
//                   .prop_map(|vals| Value(SymValueImpl::new_container(SymContainerImpl::U64(vals))))
//                   .boxed(),
//               Type::U128 => vec(any::<u128>(), 0..10)
//                   .prop_map(|vals| Value(SymValueImpl::new_container(SymContainerImpl::U128(vals))))
//                   .boxed(),
//               Type::Bool => vec(any::<bool>(), 0..10)
//                   .prop_map(|vals| Value(SymValueImpl::new_container(SymContainerImpl::Bool(vals))))
//                   .boxed(),
//               layout => vec(value_strategy_with_layout(layout), 0..10)
//                   .prop_map(|vals| {
//                       Value(SymValueImpl::new_container(SymContainerImpl::General(
//                           vals.into_iter().map(|val| val.0).collect(),
//                       )))
//                   })
//                   .boxed(),
//           },

//           Type::Struct(StructDef::Struct(inner)) => inner
//               .field_definitions()
//               .iter()
//               .map(|layout| value_strategy_with_layout(layout))
//               .collect::<Vec<_>>()
//               .prop_map(|vals| {
//                   Value(SymValueImpl::new_container(SymContainerImpl::General(
//                       vals.into_iter().map(|val| val.0).collect(),
//                   )))
//               })
//               .boxed(),

//           Type::Reference(..) | Type::MutableReference(..) => {
//               panic!("cannot generate references for prop tests")
//           }

//           Type::TypeVariable(..) => panic!("cannot generate type variables for prop tests"),
//       }
//   }

//   pub fn layout_and_value_strategy() -> impl Strategy<Value = (Type, Value)> {
//       any::<Type>().no_shrink().prop_flat_map(|layout| {
//           let value_strategy = value_strategy_with_layout(&layout);
//           (Just(layout), value_strategy)
//       })
//   }
// }
