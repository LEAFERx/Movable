use diem_types::{
  account_address::AccountAddress,
};
use move_core_types::{
  gas_schedule::{
    AbstractMemorySize, GasAlgebra, GasCarrier, InternalGasUnits, CONST_SIZE,
    REFERENCE_SIZE, MIN_EXISTS_DATA_SIZE, 
  },
  language_storage::{StructTag, TypeTag},
  value::MoveTypeLayout,
  vm_status::{
    sub_status::NFE_VECTOR_ERROR_BASE, StatusCode,
  },
};
use move_vm_types::{
  // gas_schedule::NativeCostIndex,
  // natives::function::native_gas,
  loaded_data::runtime_types::Type,
  values::{Struct, VMValueCast, Value},
};
use std::{
  cell::RefCell,
  fmt::{self, Debug, Display},
  iter,
  rc::Rc,
};
use vm::{
  errors::*,
  file_format::{Constant, SignatureToken},
};

use z3::{
  ast::{Ast, Array, BV, Datatype, Dynamic},
  Context,
  DatatypeSort,
  Sort,
};

use crate::{
  types::{
    natives::{SymNativeContext, SymNativeResult},
    values::{
      account_address::SymAccountAddress,
      primitives::{SymBool, SymU128, SymU64, SymU8},
      sort::*,
      SymbolicMoveValue,
    },
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
enum SymValueImpl<'ctx> {
  Invalid,

  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
  Bool(SymBool<'ctx>),
  Address(SymAccountAddress<'ctx>),

  Container(SymContainer<'ctx>),

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
#[derive(Debug, Clone)]
enum SymContainer<'ctx> {
  Locals(Rc<RefCell<Vec<SymValueImpl<'ctx>>>>),
  Vec(Rc<RefCell<SymVectorImpl<'ctx>>>),
  Struct(Rc<RefCell<SymStructImpl<'ctx>>>),
  VecU8(Rc<RefCell<SymVectorImpl<'ctx>>>),
  VecU64(Rc<RefCell<SymVectorImpl<'ctx>>>),
  VecU128(Rc<RefCell<SymVectorImpl<'ctx>>>),
  VecBool(Rc<RefCell<SymVectorImpl<'ctx>>>),
  VecAddress(Rc<RefCell<SymVectorImpl<'ctx>>>),
}

/// A ContainerRef is a direct reference to a container, which could live either in the frame
/// or in global storage. In the latter case, it also keeps a status flag indicating whether
/// the container has been possibly modified.
/// The location is used for Struct and Vector
#[derive(Debug)]
enum SymContainerRef<'ctx> {
  Local {
    container: SymContainer<'ctx>,
    location: SymContainerRefLocation<'ctx>,
  },
  Global {
    status: Rc<RefCell<GlobalDataStatus>>,
    container: SymContainer<'ctx>,
    location: SymContainerRefLocation<'ctx>,
  },
}

/// For write propagation
#[derive(Debug)]
enum SymContainerRefLocation<'ctx> {
  Independent,
  Dependent {
    idx: SymbolicContainerIndex<'ctx>,
    loc: Box<SymContainerRef<'ctx>>,
  }
}

/// Status for global (on-chain) data:
/// Clean - the data was only read.
/// Dirty - the data was possibly modified.
#[derive(Debug, Clone, Copy)]
enum GlobalDataStatus {
  Clean,
  Dirty,
}

// Symbolic is used on vector, while Concrete is used on locals and struct
// According to Move design, we won't use Concrete on vector, but currently
// Movable supports it.
// TODO: evaluate this.
#[derive(Debug)]
enum SymbolicContainerIndex<'ctx> {
  Concrete(usize),
  Symbolic(SymU64<'ctx>),
}

/// A Move reference pointing to an element in a container.
#[derive(Debug)]
struct SymIndexedRef<'ctx> {
  idx: SymbolicContainerIndex<'ctx>,
  container_ref: SymContainerRef<'ctx>,
}

/// An umbrella enum for references. It is used to hide the internals of the public type
/// Reference.
#[derive(Debug)]
enum SymReferenceImpl<'ctx> {
  IndexedRef(SymIndexedRef<'ctx>),
  ContainerRef(SymContainerRef<'ctx>),
}

#[derive(Debug)]
struct SymStructImpl<'ctx> {
  z3_ctx: &'ctx Context,
  struct_type: StructTag,
  datatype: Rc<RefCell<DatatypeSort<'ctx>>>,
  data: Datatype<'ctx>,
}

#[derive(Debug)]
pub(crate) struct SymVectorImpl<'ctx> {
  z3_ctx: &'ctx Context,
  element_type: TypeTag,
  datatype: Rc<RefCell<DatatypeSort<'ctx>>>,
  data: Datatype<'ctx>,
}

// A reference to a signer. Clients can attempt a cast to this struct if they are
// expecting a Signer on the stack or as an argument.
#[derive(Debug)]
pub struct SymSignerRef<'ctx>(SymContainerRef<'ctx>);

// A reference to a vector. This is an alias for a ContainerRef for now but we may change
// it once Containers are restructured.
// It's used from vector native functions to get a reference to a vector and operate on that.
// There is an impl for VecotrRef which implements the API private to this module.
#[derive(Debug)]
pub struct SymVectorRef<'ctx>(SymContainerRef<'ctx>);

// A vector. This is an alias for a Container for now but we may change
// it once Containers are restructured.
// It's used from vector native functions to get a vector and operate on that.
// There is an impl for Vecotr which implements the API private to this module.
#[derive(Debug)]
pub struct SymVector<'ctx>(SymContainer<'ctx>);

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
pub struct SymLocals<'ctx>(Rc<RefCell<Vec<SymValueImpl<'ctx>>>>);

/// An integer value in Move.
#[derive(Debug)]
pub enum SymIntegerValue<'ctx> {
  U8(SymU8<'ctx>),
  U64(SymU64<'ctx>),
  U128(SymU128<'ctx>),
}

/// A Move struct.
#[derive(Debug)]
pub struct SymStruct<'ctx>(SymStructImpl<'ctx>);

/// A special "slot" in global storage that can hold a resource. It also keeps track of the status
/// of the resource relative to the global state, which is necessary to compute the effects to emit
/// at the end of transaction execution.
#[derive(Debug)]
enum SymGlobalValueImpl<'ctx> {
  /// No resource resides in this slot or in storage.
  None,
  /// A resource has been published to this slot and it did not previously exist in storage.
  Fresh { resource: SymContainer<'ctx> },
  /// A resource resides in this slot and also in storage. The status flag indicates whether
  /// it has potentially been altered.
  Cached {
    resource: SymContainer<'ctx>,
    status: Rc<RefCell<GlobalDataStatus>>,
  },
  /// A resource used to exist in storage but has been deleted by the current transaction.
  Deleted,
}

/// A wrapper around `GlobalValueImpl`, representing a "slot" in global storage that can
/// hold a resource.
#[derive(Debug)]
pub struct SymGlobalValue<'ctx>(SymGlobalValueImpl<'ctx>);

/// Simple enum for the change state of a GlobalValue, used by `into_effect`.
pub enum SymGlobalValueEffect<T> {
  /// There was no value, or the value was not changed
  None,
  /// The value was removed
  Deleted,
  /// Updated with a new value
  Changed(T),
}

/***************************************************************************************
*
* Misc
*
*   Miscellaneous helper functions.
*
**************************************************************************************/
impl<'ctx> SymStructImpl<'ctx> {
  fn len(&self) -> usize {
    self.datatype.borrow().variants[0].accessors.len()
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn len(&self) -> usize {
    use SymContainer::*;

    match self {
      // TODO: figure it out
      Locals(r) => r.borrow().len(),
      Struct(r) => r.borrow().len(),
      Vec(_v) => 0, // v.len(),
      VecU8(_v) => 0, // v.len(),
      VecU64(_v) => 0, // v.len(),
      VecU128(_v) => 0, // v.len(),
      VecBool(_v) => 0, // v.len(),
      VecAddress(_v) => 0, // v.len(),
    }
  }

  fn rc_count(&self) -> usize {
    use SymContainer::*;

    match self {
      Locals(r) => Rc::strong_count(r),
      Struct(r) => Rc::strong_count(r),
      Vec(r) | VecU8(r) | VecU64(r) | VecU128(r) | VecBool(r) | VecAddress(r)
        => Rc::strong_count(r),
    }
  }

  // TODO: Figure out the signer struct symbolization
  fn signer(x: SymAccountAddress<'ctx>) -> Self {
    let ast = x.as_ast().unwrap();
    let z3_ctx = ast.get_ctx();
    let inner = SymStructImpl::signer(z3_ctx, &ast);
    SymContainer::Struct(Rc::new(RefCell::new(inner)))
  }
}

impl<'ctx> SymbolicContainerIndex<'ctx> {
  fn to_concrete(&self) -> Option<usize> {
    use SymbolicContainerIndex::*;

    match self {
      Concrete(idx) => Some(*idx),
      Symbolic(_) => None,
    }
  }
}

macro_rules! get_local_by_idx {
  ($locals: expr, $idx: expr) => {
    {
      let idx = $idx.to_concrete().ok_or(
        PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
          .with_message(format!("Symbolic index {:?} cannot be used on Locals", $idx))
      )?;
      &$locals[idx]
    }
  };
}

macro_rules! set_local_by_idx {
  ($locals: expr, $idx: expr, $val: expr) => {
    {
      let idx = $idx.to_concrete().ok_or(
        PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
          .with_message(format!("Symbolic index {:?} cannot be used on Locals", $idx))
      )?;
      $locals[idx] = $val;
    }
  };
}

impl<'ctx> SymStructImpl<'ctx> {
  fn new(
    z3_ctx: &'ctx Context,
    struct_type: StructTag,
    fields: &[&Dynamic<'ctx>],
  ) -> Self {
    let datatype = struct_tag_to_datatype_sort(z3_ctx, &struct_type);
    let data = datatype.variants[0].constructor.apply(fields).as_datatype().unwrap();
    SymStructImpl {
      z3_ctx,
      struct_type,
      datatype: Rc::new(RefCell::new(datatype)),
      data,
    }
  }

  fn signer(z3_ctx: &'ctx Context, addr: &Dynamic<'ctx>) -> Self {
    let datatype = signer_sort(z3_ctx);
    let data = datatype.variants[0].constructor.apply(&[addr]).as_datatype().unwrap();
    SymStructImpl {
      z3_ctx,
      struct_type: signer_tag(),
      datatype: Rc::new(RefCell::new(datatype)),
      data,
    }
  }

  fn from_ast(z3_ctx: &'ctx Context, struct_type: &StructTag, ast: Datatype<'ctx>) -> Self {
    let datatype = struct_tag_to_datatype_sort(z3_ctx, struct_type);
    Self {
      z3_ctx,
      struct_type: struct_type.clone(),
      datatype: Rc::new(RefCell::new(datatype)),
      data: ast,
    }
  }

  fn from_signer_ast(z3_ctx: &'ctx Context, ast: Datatype<'ctx>) -> Self {
    Self {
      z3_ctx,
      struct_type: signer_tag(),
      datatype: Rc::new(RefCell::new(signer_sort(z3_ctx))),
      data: ast,
    }
  }

  fn get_raw(&self, idx: usize) -> PartialVMResult<Dynamic<'ctx>> {
    if idx > self.len() {
      return Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot access invalid value at index {}", idx))
      );
    }
    Ok(self.datatype.borrow().variants[0].accessors[idx].apply(&[&Dynamic::from_ast(&self.data)]))
  }

  fn set_raw(&mut self, idx: usize, val: Dynamic<'ctx>) -> PartialVMResult<()> {
    // TODO: find a better way to set, maybe try to improve z3.rs
    let len = self.len();
    let mut fields = Vec::with_capacity(len);
    for i in 0..len {
      if i == idx {
        // Clone here is actually unnecessary but needed
        // But clone on ast is just a shallow copy, so it is correct
        fields.push(val.clone());
      } else {
        fields.push(self.get_raw(i)?);
      }
    }
    let field_refs = fields.iter().collect::<Vec<_>>();
    self.data = self
      .datatype.borrow()
      .variants[0].constructor.apply(field_refs.as_slice())
      .as_datatype().unwrap();
    Ok(())
  }

  fn get(&self, idx: &SymbolicContainerIndex<'ctx>) -> PartialVMResult<SymValue<'ctx>> {
    let idx = idx.to_concrete().ok_or(
      PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.type_params[idx];
    SymValue::from_ast_with_type(self.z3_ctx, ast, ty)
  }

  fn set(&mut self, idx: &SymbolicContainerIndex<'ctx>, val: SymValue<'ctx>) -> PartialVMResult<()> {
    let idx = idx.to_concrete().ok_or(
      PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    // TODO: should check type here
    self.set_raw(idx, val.as_ast()?)?;
    Ok(())
  }
  
  fn pack<I: IntoIterator<Item = SymValue<'ctx>>>(
    z3_ctx: &'ctx Context,
    struct_type: &StructTag,
    values: I
  ) -> PartialVMResult<Self> {
    let fields = values.into_iter()
      .map(|v| v.as_ast()).collect::<PartialVMResult<Vec<_>>>()?;
    let field_refs = fields.iter().collect::<Vec<_>>();
    Ok(Self::new(
      z3_ctx,
      struct_type.clone(),
      field_refs.as_slice(),
    ))
  }

  fn get_internal(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.type_params[idx];
    Ok(SymValue::from_ast_with_type(self.z3_ctx, ast, ty)?)
  }

  fn unpack(self) -> PartialVMResult<Vec<SymValue<'ctx>>> {
    let mut values = vec![];
    for idx in 0..self.struct_type.type_params.len() {
      values.push(self.get_internal(idx)?);
    }
    Ok(values)
  }
}

impl<'ctx> SymVectorImpl<'ctx> {
  fn make(&self, array: &Array<'ctx>, len: &BV<'ctx>) -> Datatype<'ctx> {
    let array = Dynamic::from_ast(array);
    let len = Dynamic::from_ast(len);
    self.datatype.borrow()
      .variants[0].constructor.apply(&[&array, &len])
      .as_datatype().unwrap()
  }

  fn array(&self) -> Array<'ctx> {
    let data = Dynamic::from_ast(&self.data);
    self.datatype.borrow()
      .variants[0].accessors[0]
      .apply(&[&data]).as_array().unwrap()
  }

  fn symlen(&self) -> BV<'ctx> {
    let data = Dynamic::from_ast(&self.data);
    self.datatype.borrow()
      .variants[0].accessors[1]
      .apply(&[&data]).as_bv().unwrap()
  }

  fn set_array(&mut self, array: &Array<'ctx>) {
    self.data = self.make(array, &self.symlen());
  }

  fn set_symlen(&mut self, len: &BV<'ctx>) {
    self.data = self.make(&self.array(), len);
  }

  fn get_raw(&self, idx: &BV<'ctx>) -> Dynamic<'ctx> {
    self.array().select(idx)
  }

  fn set_raw(&mut self, idx: &BV<'ctx>, val: &Dynamic<'ctx>) {
    let arr = self.array().store(idx, val);
    self.set_array(&arr);
  }
  
  fn set_multiple_raw(&mut self, idx_val_pairs: &[(&BV<'ctx>, &Dynamic<'ctx>)]) {
    let mut v = self.array();
    for (idx, val) in idx_val_pairs {
      v = v.store(*idx, *val);
    }
    self.set_array(&v.into());
  }

  fn new(
    z3_ctx: &'ctx Context,
    element_type: &TypeTag,
    values: &[&Dynamic<'ctx>],
  ) -> Self {
    let range_sort = type_tag_to_sort(z3_ctx, element_type);
    let vector_datatypesort = vec_to_datatype_sort(z3_ctx, element_type);

    let mut arr = Array::fresh_const(z3_ctx, "vector", &Sort::bitvector(z3_ctx, 64), &range_sort);
    for i in 0..values.len() {
      arr = arr.store(&BV::from_u64(z3_ctx, i as u64, 64), values[i]);
    }
    let symlen = BV::from_u64(z3_ctx, values.len() as u64, 64);
    let data = vector_datatypesort
      .variants[0].constructor.apply(&[&arr.into(), &symlen.into()])
      .as_datatype().unwrap();

    Self {
      z3_ctx,
      element_type: element_type.clone(),
      datatype: Rc::new(RefCell::new(vector_datatypesort)),
      data,
    }
  }

  fn get(&self, idx: &SymbolicContainerIndex<'ctx>) -> PartialVMResult<SymValue<'ctx>> {
    use SymbolicContainerIndex::*;

    let ast = match idx {
      Concrete(idx) => {
        let idx = BV::from_u64(self.z3_ctx, *idx as u64, 64);
        self.get_raw(&idx)
      },
      Symbolic(idx) => self.get_raw(&idx.as_inner()),
    };
    let ty = &self.element_type;
    Ok(SymValue::from_ast_with_type(self.z3_ctx, ast, ty)?)
  }
  
  fn set(
    &mut self,
    idx: &SymbolicContainerIndex<'ctx>,
    val: SymValue<'ctx>
  ) -> PartialVMResult<()> {
    use SymbolicContainerIndex::*;

    match idx {
      Concrete(idx) => {
        let idx = BV::from_u64(self.z3_ctx, *idx as u64, 64);
        self.set_raw(&idx, &val.as_ast()?);
      },
      Symbolic(idx) => self.set_raw(&idx.as_inner(), &val.as_ast()?),
    };
    Ok(())
  }

  fn from_ast(z3_ctx: &'ctx Context, element_type: &TypeTag, ast: Datatype<'ctx>) -> Self {
    let vector_datatypesort = vec_to_datatype_sort(z3_ctx, element_type);
    Self {
      z3_ctx,
      element_type: element_type.clone(),
      datatype: Rc::new(RefCell::new(vector_datatypesort)),
      data: ast,
    }
  }

  fn empty(z3_ctx: &'ctx Context, element_type: &TypeTag) -> Self {
    Self::new(z3_ctx, element_type, &[])
  }

  fn push(&mut self, val: &Dynamic<'ctx>) {
    let len = self.symlen();
    let v = self.array();
    let v = v.store(&Dynamic::from_ast(&len), val);
    let updated_len = len.bvadd(&BV::from_u64(self.z3_ctx, 1, 64)).simplify();
    self.data = self.make(&v.into(), &updated_len.into());
  }
  
  fn pop(&mut self) -> Dynamic<'ctx> {
    let len = self.symlen();
    let updated_len = len.bvsub(&BV::from_u64(self.z3_ctx, 1, 64)).simplify();
    self.set_symlen(&updated_len);
    let v = self.array();
    v.select(&updated_len)
  }

  fn swap(&mut self, idx1: &SymU64<'ctx>, idx2: &SymU64<'ctx>) {
    let idx1 = idx1.as_inner();
    let idx2 = idx2.as_inner();
    let ast1 = self.get_raw(idx1);
    let ast2 = self.get_raw(idx2);
    self.set_multiple_raw(&[(idx2, &ast1), (idx1, &ast2)]);
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

fn take_unique_ownership<T: Debug>(r: Rc<RefCell<T>>) -> PartialVMResult<T> {
  match Rc::try_unwrap(r) {
    Ok(cell) => Ok(cell.into_inner()),
    Err(r) => Err(
      PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
        .with_message(format!("moving value {:?} with dangling references", r)),
    ),
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn container(&self) -> &SymContainer<'ctx> {
    match self {
      Self::Local { container, .. } | Self::Global { container, ..} => container
    }
  }

  fn mark_dirty(&self) {
    if let Self::Global { status, .. } = self {
      *status.borrow_mut() = GlobalDataStatus::Dirty;
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
  fn value_ref(&self) -> PartialVMResult<&T>;
}

macro_rules! impl_vm_value_ref {
  ($ty: ty, $tc: ident) => {
    impl<'ctx> VMValueRef<$ty> for SymValueImpl<'ctx> {
      fn value_ref(&self) -> PartialVMResult<&$ty> {
        match self {
          SymValueImpl::$tc(x) => Ok(x),
          _ => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot take {:?} as &{}", self, stringify!($ty)))),
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
  fn as_value_ref<T>(&self) -> PartialVMResult<&T>
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
  fn copy_value(&self) -> PartialVMResult<Self> {
    use SymValueImpl::*;

    Ok(match self {
      Invalid => Invalid,

      U8(x) => U8(x.clone()),
      U64(x) => U64(x.clone()),
      U128(x) => U128(x.clone()),
      Bool(x) => Bool(x.clone()),
      Address(x) => Address(x.clone()),

      ContainerRef(r) => ContainerRef(r.copy_value()),
      IndexedRef(r) => IndexedRef(r.copy_value()),

      // When cloning a container, we need to make sure we make a deep
      // copy of the data instead of a shallow copy of the Rc.
      Container(c) => Container(c.copy_value()?),
    })
  }
}

impl<'ctx> SymStructImpl<'ctx> {
  fn copy_value(&self) -> Self {
    Self {
      z3_ctx: self.z3_ctx,
      struct_type: self.struct_type.clone(),
      datatype: Rc::clone(&self.datatype),
      data: self.data.clone(),
    }
  }
}

impl<'ctx> SymVectorImpl<'ctx> {
  fn copy_value(&self) -> Self {
    Self {
      z3_ctx: self.z3_ctx,
      element_type: self.element_type.clone(),
      datatype: Rc::clone(&self.datatype),
      data: self.data.clone(),
    }
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn copy_value(&self) -> PartialVMResult<Self> {
    use SymContainer::*;

    Ok(match self {
      Struct(r) => Struct(Rc::new(RefCell::new(r.borrow().copy_value()))),
      Vec(r) => Vec(Rc::new(RefCell::new(r.borrow().copy_value()))),
      VecU8(r) => VecU8(Rc::new(RefCell::new(r.borrow().copy_value()))),
      VecU64(r) => VecU64(Rc::new(RefCell::new(r.borrow().copy_value()))),
      VecU128(r) => VecU128(Rc::new(RefCell::new(r.borrow().copy_value()))),
      VecBool(r) => VecBool(Rc::new(RefCell::new(r.borrow().copy_value()))),
      VecAddress(r) => VecAddress(Rc::new(RefCell::new(r.borrow().copy_value()))),

      Locals(_) => {
        return Err(
          PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message("cannot copy a Locals container".to_string()),
        )
      },
    })
  }

  fn copy_by_ref(&self) -> Self {
    use SymContainer::*;

    match self {
      Struct(r) => Struct(Rc::clone(r)),
      Vec(r) => Vec(Rc::clone(r)),
      VecU8(r) => VecU8(Rc::clone(r)),
      VecU64(r) => VecU64(Rc::clone(r)),
      VecU128(r) => VecU128(Rc::clone(r)),
      VecBool(r) => VecBool(Rc::clone(r)),
      VecAddress(r) => VecAddress(Rc::clone(r)),
      Locals(r) => Locals(Rc::clone(r)),
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

impl<'ctx> SymContainerRefLocation<'ctx> {
  fn copy_value(&self) -> Self {
    use SymContainerRefLocation::*;

    match self {
      Independent => Independent,
      Dependent { idx, loc } => Dependent {
        idx: idx.copy_value(),
        loc: Box::new(loc.copy_value()),
      },
    }
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn copy_value(&self) -> Self {
    match self {
      Self::Local { container, location } => Self::Local {
        container: container.copy_by_ref(),
        location: location.copy_value(),
      },
      Self::Global { status, container, location } => Self::Global {
        status: Rc::clone(status),
        container: container.copy_by_ref(),
        location: location.copy_value(),
      },
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn copy_value(&self) -> PartialVMResult<Self> {
    Ok(Self(self.0.copy_value()?))
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
  fn equals(&self, other: &Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymValueImpl::*;

    let res = match (self, other) {
      (U8(l), U8(r)) => l.equals(r),
      (U64(l), U64(r)) => l.equals(r),
      (U128(l), U128(r)) => l.equals(r),
      (Bool(l), Bool(r)) => l.equals(r),
      (Address(l), Address(r)) => l.equals(r),

      (Container(l), Container(r)) => l.equals(r)?,

      (ContainerRef(l), ContainerRef(r)) => l.equals(r)?,
      (IndexedRef(l), IndexedRef(r)) => l.equals(r)?,

      _ => {
        return Err(
          PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot compare values: {:?}, {:?}", self, other)),
        )
      }
    };

    Ok(res)
  }
}

impl<'ctx> SymStructImpl<'ctx> {
  fn equals(&self, other: &Self) -> SymBool<'ctx> {
    if self.len() != other.len() {
      SymBool::from(self.z3_ctx, false);
    }
    SymBool::from_ast(self.data._eq(&other.data))
  }
}

impl<'ctx> SymVectorImpl<'ctx> {
  fn equals(&self, other: &Self) -> SymBool<'ctx> {
    SymBool::from_ast(self.data._eq(&other.data))
  }
}

impl<'ctx> SymContainer<'ctx> {
  fn equals(&self, other: &Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymContainer::*;

    let res = match (&self, &other) {
      (Struct(l), Struct(r)) => l.borrow().equals(&*r.borrow()),
      (Vec(l), Vec(r)) 
      | (VecU8(l), VecU8(r))
      | (VecU64(l), VecU64(r))
      | (VecU128(l), VecU128(r))
      | (VecBool(l), VecBool(r))
      | (VecAddress(l), VecAddress(r))
      => l.borrow().equals(&*r.borrow()),
      _ => {
        return Err(
          PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
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
  fn equals(&self, other: &Self) -> PartialVMResult<SymBool<'ctx>> {
    self.container().equals(other.container())
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  // TODO: Carefully revise it!
  // This function may not implement exact the same semantics of `equals` as the `SymContainer` is using
  // data structure like current(2020.08.24) Move but symplified. However, it should be ok in most cases.
  fn equals(&self, other: &Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymContainer::*;

    macro_rules! eq {
      ($r1: expr) => {
        match other.container_ref.container() {
          Locals(r2) => $r1.equals(get_local_by_idx!(r2.borrow(), other.idx)),
          Struct(r2) => $r1.equals(&r2.borrow().get(&other.idx)?.0),
          Vec(r2)
          | VecU8(r2)
          | VecU64(r2)
          | VecU128(r2)
          | VecBool(r2)
          | VecAddress(r2) => $r1.equals(&r2.borrow().get(&other.idx)?.0),
        }
      };
    }

    match self.container_ref.container() {
      Locals(r) => {
        let idx = self.idx.to_concrete().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("Symbolic index {:?} cannot be used on Locals", self.idx))
        )?;
        eq!(r.borrow()[idx])
      },
      Struct(r) => eq!(r.borrow().get(&self.idx)?.0),
      Vec(r)
      | VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r)=> eq!(r.borrow().get(&self.idx)?.0),
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn equals(&self, other: &Self) -> PartialVMResult<SymBool<'ctx>> {
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
  fn read_ref(self) -> PartialVMResult<SymValue<'ctx>> {
    Ok(SymValue(SymValueImpl::Container(self.container().copy_value()?)))
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn read_ref(self) -> PartialVMResult<SymValue<'ctx>> {
    use SymContainer::*;

    let res = match &*self.container_ref.container() {
      Locals(r) => SymValue(get_local_by_idx!(r.borrow(), self.idx).copy_value()?),
      Struct(r) => r.borrow().get(&self.idx)?,
      Vec(r)
      | VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r) => r.borrow().get(&self.idx)?,
    };

    Ok(res)
  }
}

impl<'ctx> SymReferenceImpl<'ctx> {
  fn read_ref(self) -> PartialVMResult<SymValue<'ctx>> {
    match self {
      Self::ContainerRef(r) => r.read_ref(),
      Self::IndexedRef(r) => r.read_ref(),
    }
  }
}

impl<'ctx> SymStructRef<'ctx> {
  pub fn read_ref(self) -> PartialVMResult<SymValue<'ctx>> {
    self.0.read_ref()
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn read_ref(self) -> PartialVMResult<SymValue<'ctx>> {
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
impl<'ctx> SymContainerRefLocation<'ctx> {
  fn write_propagate(&self, v: SymValue<'ctx>) -> PartialVMResult<()> {
    match self {
      Self::Independent => Ok(()),
      Self::Dependent { idx, loc } => {
        use SymContainer::*;
        match loc.container() {
          Locals(_) => {
            return Err(
              PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                .with_message(format!("Locals should not be the target of write propagation")),
            )
          },
          Struct(r) => r.borrow_mut().set(idx, v)?,
          Vec(r) | VecU8(r) | VecU64(r) | VecU128(r) | VecBool(r) | VecAddress(r)
            => r.borrow_mut().set(idx, v)?,
        }
        Ok(())
      }
    }
  }
}

impl<'ctx> SymContainerRef<'ctx> {
  fn write_propagate(&self) -> PartialVMResult<()> {
    let loc = match self {
      Self::Local { location, .. } => location,
      Self::Global { location, .. } => location,
    };
    loc.write_propagate(self.copy_value().read_ref()?)
  }

  fn write_ref(self, v: SymValue<'ctx>) -> PartialVMResult<()> {
    match v.0 {
      SymValueImpl::Container(c) => {
        use SymContainer::*;

        macro_rules! assign {
          ($r1: expr, $tc: ident) => {{
            let r = match c {
              $tc(v) => v,
              _ => {
                return Err(PartialVMError::new(
                  StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
                )
                .with_message(
                    "failed to write_ref: container type mismatch".to_string(),
                ))
              }
            };
            *$r1.borrow_mut() = take_unique_ownership(r)?;
          }};
        }

        match self.container() {
          Struct(r) => assign!(r, Struct),
          Vec(r) => assign!(r, Vec),
          VecU8(r) => assign!(r, VecU8),
          VecU64(r) => assign!(r, VecU64),
          VecU128(r) => assign!(r, VecU128),
          VecBool(r) => assign!(r, VecBool),
          VecAddress(r) => assign!(r, VecAddress),
          Locals(_) => {
            return Err(PartialVMError::new(
              StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
            )
            .with_message("cannot overwrite Container::Locals".to_string()))
          },
        }
        self.write_propagate()?;
        self.mark_dirty();
      }
      _ => {
        return Err(
          PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
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
  fn write_ref(self, x: SymValue<'ctx>) -> PartialVMResult<()> {
    match &x.0 {
      SymValueImpl::IndexedRef(_)
      | SymValueImpl::ContainerRef(_)
      | SymValueImpl::Invalid
      | SymValueImpl::Container(_) => {
        return Err(
          PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
      _ => (),
    }

    match (self.container_ref.container(), &x.0) {
      (SymContainer::Locals(r), _) => set_local_by_idx!(r.borrow_mut(), self.idx, x.0),
      (SymContainer::Struct(r), _) => r.borrow_mut().set(&self.idx, x)?,
      (SymContainer::Vec(r), _)
      | (SymContainer::VecU8(r), SymValueImpl::U8(_))
      | (SymContainer::VecU64(r), SymValueImpl::U64(_))
      | (SymContainer::VecU128(r), SymValueImpl::U128(_))
      | (SymContainer::VecBool(r), SymValueImpl::Bool(_))
      | (SymContainer::VecAddress(r), SymValueImpl::Address(_)) => r.borrow_mut().set(&self.idx, x)?,
      _ => {
        return Err(
          PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!(
            "cannot write value {:?} to indexed ref {:?}",
            x, self
          )),
        )
      }
    }
    self.container_ref.write_propagate()?;
    self.container_ref.mark_dirty();
    Ok(())
  }
}

impl<'ctx> SymReferenceImpl<'ctx> {
  fn write_ref(self, x: SymValue<'ctx>) -> PartialVMResult<()> {
    match self {
      Self::ContainerRef(r) => r.write_ref(x),
      Self::IndexedRef(r) => r.write_ref(x),
    }
  }
}

impl<'ctx> SymReference<'ctx> {
  pub fn write_ref(self, x: SymValue<'ctx>) -> PartialVMResult<()> {
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
  fn borrow_elem(&self, idx: SymbolicContainerIndex<'ctx>) -> PartialVMResult<SymValueImpl<'ctx>> {
    use SymbolicContainerIndex::*;
    use SymContainerRefLocation as Loc;

    let len = self.container().len();
    match &idx {
      Concrete(idx) => if *idx >= len {
        return Err(
          PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(
            format!(
              "index out of bounds when borrowing container element: got: {}, len: {}",
              idx, len
            )
          ),
        );
      },
      // Symbolic is only used on vector, check in vector::native_borrow
      Symbolic(_) => {},
    }

    // TODO: Currently except locals all ref is in indexed ref, it seems ok to me but nee further consideration.
    let res = match self.container() {
      SymContainer::Locals(r) => match get_local_by_idx!(r.borrow(), idx) {
        // TODO: check for the impossible combinations.
        SymValueImpl::Container(container) => {
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: container.copy_by_ref(),
              // Locals does not need location
              location: Loc::Independent,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: container.copy_by_ref(),
              // Locals does not need location
              location: Loc::Independent,
            },
          };
          SymValueImpl::ContainerRef(r)
        }
        _ => SymValueImpl::IndexedRef(SymIndexedRef {
          idx,
          container_ref: self.copy_value(),
        }),
      },
      SymContainer::Struct(r) => match &r.borrow().get(&idx)?.0 {
        SymValueImpl::Container(container) => {
          let location = Loc::Dependent {
            idx,
            loc: Box::new(self.copy_value())
          };
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: container.copy_by_ref(),
              location,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: container.copy_by_ref(),
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
      SymContainer::Vec(r) => match &r.borrow().get(&idx)?.0 {
        SymValueImpl::Container(container) => {
          let location = Loc::Dependent {
            idx,
            loc: Box::new(self.copy_value())
          };
          let r = match self {
            Self::Local { .. } => Self::Local {
              container: container.copy_by_ref(),
              location,
            },
            Self::Global { status, .. } => Self::Global {
              status: Rc::clone(status),
              container: container.copy_by_ref(),
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
  pub fn borrow_field(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    Ok(SymValue(self.0.borrow_elem(SymbolicContainerIndex::Concrete(idx))?))
  }
}

impl<'ctx> SymLocals<'ctx> {
  pub fn borrow_loc(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    let v = self.0.borrow();
    if idx >= v.len() {
      return Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(
          format!(
            "index out of bounds when borrowing local: got {}, len: {}",
            idx, v.len()
          )
        )
      );
    }
    match &v[idx] {
      SymValueImpl::Container(c) => Ok(SymValue(SymValueImpl::ContainerRef(SymContainerRef::Local {
        container: c.copy_by_ref(),
        location: SymContainerRefLocation::Independent,
      }))),

      SymValueImpl::U8(_)
      | SymValueImpl::U64(_)
      | SymValueImpl::U128(_)
      | SymValueImpl::Bool(_)
      | SymValueImpl::Address(_) => Ok(SymValue(SymValueImpl::IndexedRef(SymIndexedRef {
        container_ref: SymContainerRef::Local {
          container: SymContainer::Locals(Rc::clone(&self.0)),
          location: SymContainerRefLocation::Independent,
        },
        idx: SymbolicContainerIndex::Concrete(idx),
      }))),

      SymValueImpl::ContainerRef(_) | SymValueImpl::Invalid | SymValueImpl::IndexedRef(_) => Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot borrow local {:?}", &v[idx])),
      ),
    }
  }
}

impl<'ctx> SymSignerRef<'ctx> {
  pub fn borrow_signer(&self) -> PartialVMResult<SymValue<'ctx>> {
    Ok(SymValue(self.0.borrow_elem(SymbolicContainerIndex::Concrete(0))?))
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
  pub fn new(z3_ctx: &'ctx Context, n: usize) -> Self {
    Self(Rc::new(RefCell::new(
      iter::repeat_with(|| SymValueImpl::Invalid).take(n).collect(),
    )))
  }

  pub fn fork(&self) -> Self {
    Self(Rc::new(RefCell::new(
      self.0.borrow().iter().map(|val| val.copy_value().unwrap()).collect()
    )))
  }

  pub fn copy_loc(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    let v = self.0.borrow();
    match v.get(idx) {
      Some(SymValueImpl::Invalid) => Err(PartialVMError::new(
          StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
        )
        .with_message(format!("cannot copy invalid value at index {}", idx))),
      Some(v) => Ok(SymValue(v.copy_value()?)),
      None => Err(
        PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
          format!("local index out of bounds: got {}, len: {}", idx, v.len()),
        ),
      ),
    }
  }

  fn swap_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> PartialVMResult<SymValue<'ctx>> {
    let mut v = self.0.borrow_mut();
    match v.get_mut(idx) {
      Some(v) => {
        if let SymValueImpl::Container(c) = v {
          if c.rc_count() > 1 {
            return Err(PartialVMError::new(
              StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
            )
            .with_message("moving container with dangling references".to_string()));
          }
        }
        Ok(SymValue(std::mem::replace(v, x.0)))
      }
      None => Err(
        PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
          format!("local index out of bounds: got {}, len: {}", idx, v.len()),
        ),
      ),
    }
  }

  pub fn move_loc(&mut self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    match self.swap_loc(idx, SymValue(SymValueImpl::Invalid))? {
      SymValue(SymValueImpl::Invalid) => Err(PartialVMError::new(
        StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
      )
      .with_message(format!("cannot move invalid value at index {}", idx))),
      v => Ok(v)
    }
  }

  pub fn store_loc(&mut self, idx: usize, x: SymValue<'ctx>) -> PartialVMResult<()> {
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
  pub fn from_deserialized_value(
    z3_ctx: &'ctx Context,
    value: Value,
    ty: &TypeTag,
  ) -> PartialVMResult<Self> {
    match ty {
      TypeTag::Bool => Ok(SymValue::from_bool(z3_ctx, value.value_as()?)),
      TypeTag::U8 => Ok(SymValue::from_u8(z3_ctx, value.value_as()?)),
      TypeTag::U64 => Ok(SymValue::from_u64(z3_ctx, value.value_as()?)),
      TypeTag::U128 => Ok(SymValue::from_u128(z3_ctx, value.value_as()?)),
      TypeTag::Address => Ok(SymValue::from_address(z3_ctx, value.value_as()?)),
      TypeTag::Vector(_) => unimplemented!(),
      TypeTag::Struct(struct_type) => Ok(SymValue::from_deserialized_struct(
        z3_ctx,
        VMValueCast::cast(value)?,
        struct_type,
      )?),
      TypeTag::Signer => Ok(SymValue::signer(z3_ctx, value.value_as()?)),
    }
  }

  pub fn from_ast_with_type(
    z3_ctx: &'ctx Context,
    ast: Dynamic<'ctx>,
    ty: &TypeTag
  ) -> PartialVMResult<Self> {
    match ty {
      TypeTag::Bool => {
        let ast = ast.as_bool().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into Bool", ast))
        )?;
        Ok(SymValue::from_sym_bool(SymBool::from_ast(ast)))
      }
      TypeTag::U8 => {
        let ast = ast.as_bv().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into U8", ast))
        )?;
        Ok(SymValue::from_sym_u8(SymU8::from_ast(ast)))
      }
      TypeTag::U64 => {
        let ast = ast.as_bv().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into U64", ast))
        )?;
        Ok(SymValue::from_sym_u64(SymU64::from_ast(ast)))
      }
      TypeTag::U128 => {
        let ast = ast.as_bv().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into U128", ast))
        )?;
        Ok(SymValue::from_sym_u128(SymU128::from_ast(ast)))
      }
      TypeTag::Address => {
        let ast = ast.as_bv().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into Address", ast))
        )?;
        let addr = SymAccountAddress::from_ast(ast);
        Ok(SymValue::from_sym_address(addr))
      }
      TypeTag::Vector(ty) => {
        let ast = ast.as_datatype().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into Vector", ast))
        )?;
        let res = match ty.as_ref() {
          ty @ TypeTag::U8 => SymValue::from_sym_vec_u8(SymVectorImpl::from_ast(z3_ctx, ty, ast)),
          ty @ TypeTag::U64 => SymValue::from_sym_vec_u64(SymVectorImpl::from_ast(z3_ctx, ty, ast)),
          ty @ TypeTag::U128 => SymValue::from_sym_vec_u128(SymVectorImpl::from_ast(z3_ctx, ty, ast)),
          ty @ TypeTag::Bool => SymValue::from_sym_vec_bool(SymVectorImpl::from_ast(z3_ctx, ty, ast)),
          ty @ _ => SymValue::from_sym_vector(SymVectorImpl::from_ast(z3_ctx, ty, ast)),
        };
        Ok(res)
      },
      TypeTag::Struct(layout) => {
        let ast = ast.as_datatype().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into Datatype", ast))
        )?;
        let s = SymStructImpl::from_ast(z3_ctx, layout, ast);
        Ok(SymValue::from_sym_struct_impl(s))
      },
      TypeTag::Signer => {
        let ast = ast.as_datatype().ok_or(
          PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
            .with_message(format!("{:?} can not be made into Datatype", ast))
        )?;
        let s = SymStructImpl::from_signer_ast(z3_ctx, ast);
        Ok(SymValue::from_sym_struct_impl(s))
      },
    }
  }

  pub fn from_u8(z3_ctx: &'ctx Context, value: u8) -> Self {
    SymValue(SymValueImpl::U8(SymU8::from(z3_ctx, value)))
  }

  pub fn from_sym_u8(sym: SymU8<'ctx>) -> Self {
    SymValue(SymValueImpl::U8(sym))
  }

  pub fn new_u8(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U8(SymU8::new(z3_ctx, prefix)))
  }

  pub fn from_u64(z3_ctx: &'ctx Context, value: u64) -> Self {
    SymValue(SymValueImpl::U64(SymU64::from(z3_ctx, value)))
  }

  pub fn from_sym_u64(sym: SymU64<'ctx>) -> Self {
    SymValue(SymValueImpl::U64(sym))
  }

  pub fn new_u64(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U64(SymU64::new(z3_ctx, prefix)))
  }

  pub fn from_u128(z3_ctx: &'ctx Context, value: u128) -> Self {
    SymValue(SymValueImpl::U128(SymU128::from(z3_ctx, value)))
  }

  pub fn from_sym_u128(sym: SymU128<'ctx>) -> Self {
    SymValue(SymValueImpl::U128(sym))
  }

  pub fn new_u128(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::U128(SymU128::new(z3_ctx, prefix)))
  }

  pub fn from_bool(z3_ctx: &'ctx Context, value: bool) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::from(z3_ctx, value)))
  }

  pub fn from_sym_bool(sym: SymBool<'ctx>) -> Self {
    SymValue(SymValueImpl::Bool(sym))
  }

  pub fn new_bool(z3_ctx: &'ctx Context, prefix: &str) -> Self {
    SymValue(SymValueImpl::Bool(SymBool::new(z3_ctx, prefix)))
  }

  pub fn from_address(z3_ctx: &'ctx Context, address: AccountAddress) -> Self {
    SymValue(SymValueImpl::Address(SymAccountAddress::new(
      z3_ctx, address,
    )))
  }

  pub fn from_sym_address(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Address(address))
  }

  pub fn signer(z3_ctx: &'ctx Context, address: AccountAddress) -> Self {
    SymValue::sym_signer(SymAccountAddress::new(z3_ctx, address))
  }

  pub fn sym_signer(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::signer(address)))
  }

  pub fn signer_reference(z3_ctx: &'ctx Context, address: AccountAddress) -> Self {
    SymValue::sym_signer_reference(SymAccountAddress::new(z3_ctx, address))
  }

  pub fn sym_signer_reference(address: SymAccountAddress<'ctx>) -> Self {
    SymValue(SymValueImpl::ContainerRef(SymContainerRef::Local {
      container: SymContainer::signer(address),
      location: SymContainerRefLocation::Independent,
    }))
  }

  pub fn from_deserialized_struct(
    z3_ctx: &'ctx Context,
    s: Struct,
    ty: &StructTag,
  ) -> PartialVMResult<Self> {
    let fields: Vec<SymValue> = s
      .unpack()?
      .into_iter()
      .enumerate()
      .map(|(idx, v)| SymValue::from_deserialized_value(z3_ctx, v, &ty.type_params[idx]))
      .collect::<PartialVMResult<_>>()?;
    Ok(SymValue::from_sym_struct(SymStruct::pack(z3_ctx, &ty, fields)?))
  }

  fn from_sym_struct_impl(s: SymStructImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::Struct(Rc::new(
      RefCell::new(s),
    ))))
  }

  pub fn from_sym_struct(s: SymStruct<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::Struct(Rc::new(
      RefCell::new(s.0),
    ))))
  }

  pub(crate) fn from_sym_vector(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::Vec(Rc::new(
      RefCell::new(v),
    ))))
  }

  pub(crate) fn from_sym_vec_u8(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::VecU8(Rc::new(
      RefCell::new(v),
    ))))
  }

  pub(crate) fn from_sym_vec_u64(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::VecU64(Rc::new(
      RefCell::new(v),
    ))))
  }

  pub(crate) fn from_sym_vec_u128(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::VecU128(Rc::new(
      RefCell::new(v),
    ))))
  }

  pub(crate) fn from_sym_vec_bool(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::VecBool(Rc::new(
      RefCell::new(v),
    ))))
  }

  pub(crate) fn from_sym_vec_address(v: SymVectorImpl<'ctx>) -> Self {
    SymValue(SymValueImpl::Container(SymContainer::VecAddress(Rc::new(
      RefCell::new(v),
    ))))
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
  fn cast(self) -> PartialVMResult<T>;
}

macro_rules! impl_vm_sym_value_cast {
  ($ty: ty, $tc: ident) => {
    impl<'ctx> VMSymValueCast<$ty> for SymValue<'ctx> {
      fn cast(self) -> PartialVMResult<$ty> {
        match self.0 {
          SymValueImpl::$tc(x) => Ok(x),
          v => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
            .with_message(format!("cannot cast {:?} to {}", v, stringify!($ty)))),
        }
      }
    }
  };
}

// TODO:
impl_vm_sym_value_cast!(SymU8<'ctx>, U8);
impl_vm_sym_value_cast!(SymU64<'ctx>, U64);
impl_vm_sym_value_cast!(SymU128<'ctx>, U128);
impl_vm_sym_value_cast!(SymBool<'ctx>, Bool);
impl_vm_sym_value_cast!(SymAccountAddress<'ctx>, Address);
impl_vm_sym_value_cast!(SymContainerRef<'ctx>, ContainerRef);
impl_vm_sym_value_cast!(SymIndexedRef<'ctx>, IndexedRef);

impl<'ctx> VMSymValueCast<SymIntegerValue<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymIntegerValue<'ctx>> {
    match self.0 {
      SymValueImpl::U8(x) => Ok(SymIntegerValue::U8(x)),
      SymValueImpl::U64(x) => Ok(SymIntegerValue::U64(x)),
      SymValueImpl::U128(x) => Ok(SymIntegerValue::U128(x)),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to integer", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymReference<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymReference<'ctx>> {
    match self.0 {
      SymValueImpl::ContainerRef(r) => Ok(SymReference(SymReferenceImpl::ContainerRef(r))),
      SymValueImpl::IndexedRef(r) => Ok(SymReference(SymReferenceImpl::IndexedRef(r))),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to reference", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymContainer<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymContainer<'ctx>> {
    match self.0 {
      SymValueImpl::Container(c) => Ok(c),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to container", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymStruct<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymStruct<'ctx>> {
    match self.0 {
      SymValueImpl::Container(SymContainer::Struct(r)) => Ok(SymStruct(
        take_unique_ownership(r)?,
      )),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to struct", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymStructRef<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymStructRef<'ctx>> {
    Ok(SymStructRef(VMSymValueCast::cast(self)?))
  }
}

// TODO: not very doable - unless we make another special type called bytes
// impl<'ctx> VMSymValueCast<Vec<SymU8<'ctx>>> for SymValue<'ctx> {
//   fn cast(self) -> PartialVMResult<Vec<SymU8<'ctx>>> {
//     match self.0 {
//       SymValueImpl::Container(r) => match take_unique_ownership(r)?.container {
//         SymContainer::U8(v) => Ok(v),
//         v => Err(
//           PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
//             .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
//         ),
//       },
//       v => Err(
//         PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
//           .with_message(format!("cannot cast {:?} to vector<SymU8>", v,)),
//       ),
//     }
//   }
// }

impl<'ctx> VMSymValueCast<SymSignerRef<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymSignerRef<'ctx>> {
    match self.0 {
      SymValueImpl::ContainerRef(r) => Ok(SymSignerRef(r)),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to Signer reference", v))
      )
    }
  }
}

impl<'ctx> VMSymValueCast<SymVectorRef<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymVectorRef<'ctx>> {
    match self.0 {
      SymValueImpl::ContainerRef(r) => Ok(SymVectorRef(r)),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to vector reference", v))
      )
    }
  }
}

impl<'ctx> VMSymValueCast<SymVector<'ctx>> for SymValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymVector<'ctx>> {
    match self.0 {
      SymValueImpl::Container(c) => Ok(SymVector(c)),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to vector reference", v))
      )
    }
  }
}

impl<'ctx> SymValue<'ctx> {
  pub fn value_as<T>(self) -> PartialVMResult<T>
  where
    Self: VMSymValueCast<T>,
  {
    VMSymValueCast::cast(self)
  }
}

impl<'ctx> VMSymValueCast<SymU8<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymU8<'ctx>> {
    match self {
      Self::U8(x) => Ok(x),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u8", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymU64<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymU64<'ctx>> {
    match self {
      Self::U64(x) => Ok(x),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u64", v,)),
      ),
    }
  }
}

impl<'ctx> VMSymValueCast<SymU128<'ctx>> for SymIntegerValue<'ctx> {
  fn cast(self) -> PartialVMResult<SymU128<'ctx>> {
    match self {
      Self::U128(x) => Ok(x),
      v => Err(
        PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)
          .with_message(format!("cannot cast {:?} to u128", v,)),
      ),
    }
  }
}

impl<'ctx> SymIntegerValue<'ctx> {
  pub fn value_as<T>(self) -> PartialVMResult<T>
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
  pub fn add(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::add(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::add(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::add(l, r)),
      (l, r) => {
        let msg = format!("Cannot add {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn sub(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::sub(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::sub(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::sub(l, r)),
      (l, r) => {
        let msg = format!("Cannot sub {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn mul(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::mul(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::mul(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::mul(l, r)),
      (l, r) => {
        let msg = format!("Cannot mul {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn div(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::div(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::div(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::div(l, r)),
      (l, r) => {
        let msg = format!("Cannot div {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn rem(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::rem(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::rem(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::rem(l, r)),
      (l, r) => {
        let msg = format!("Cannot rem {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_or(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_or(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_or(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_or(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_or {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_and(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_and(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_and(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_and(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_and {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn bit_xor(self, other: Self) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymIntegerValue::U8(SymU8::bit_xor(l, r)),
      (U64(l), U64(r)) => SymIntegerValue::U64(SymU64::bit_xor(l, r)),
      (U128(l), U128(r)) => SymIntegerValue::U128(SymU128::bit_xor(l, r)),
      (l, r) => {
        let msg = format!("Cannot bit_xor {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn shl(self, n_bits: SymU8<'ctx>) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shl(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shl(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shl(&n_bits)),
    })
  }

  pub fn shr(self, n_bits: SymU8<'ctx>) -> PartialVMResult<Self> {
    use SymIntegerValue::*;
    Ok(match self {
      U8(x) => SymIntegerValue::U8(x.shr(&n_bits)),
      U64(x) => SymIntegerValue::U64(x.shr(&n_bits)),
      U128(x) => SymIntegerValue::U128(x.shr(&n_bits)),
    })
  }

  pub fn lt(self, other: Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::lt(l, r),
      (U64(l), U64(r)) => SymU64::lt(l, r),
      (U128(l), U128(r)) => SymU128::lt(l, r),
      (l, r) => {
        let msg = format!("Cannot lt {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn le(self, other: Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::le(l, r),
      (U64(l), U64(r)) => SymU64::le(l, r),
      (U128(l), U128(r)) => SymU128::le(l, r),
      (l, r) => {
        let msg = format!("Cannot le {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn gt(self, other: Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::gt(l, r),
      (U64(l), U64(r)) => SymU64::gt(l, r),
      (U128(l), U128(r)) => SymU128::gt(l, r),
      (l, r) => {
        let msg = format!("Cannot gt {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
      }
    })
  }

  pub fn ge(self, other: Self) -> PartialVMResult<SymBool<'ctx>> {
    use SymIntegerValue::*;
    Ok(match (&self, &other) {
      (U8(l), U8(r)) => SymU8::ge(l, r),
      (U64(l), U64(r)) => SymU64::ge(l, r),
      (U128(l), U128(r)) => SymU128::ge(l, r),
      (l, r) => {
        let msg = format!("Cannot ge {:?} and {:?}", l, r);
        return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(msg));
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

pub const INDEX_OUT_OF_BOUNDS: u64 = NFE_VECTOR_ERROR_BASE + 1;
pub const POP_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 2;
pub const DESTROY_NON_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 3;

fn check_elem_layout<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty: &Type,
  v: &SymContainer<'ctx>,
) -> PartialVMResult<()> {
  match (ty, &v) {
    (Type::U8, SymContainer::VecU8(_))
    | (Type::U64, SymContainer::VecU64(_))
    | (Type::U128, SymContainer::VecU128(_))
    | (Type::Bool, SymContainer::VecBool(_))
    | (Type::Address, SymContainer::VecAddress(_))
    | (Type::Signer, SymContainer::Struct(_)) => Ok(()),

    (Type::Vector(_), SymContainer::Vec(_)) => Ok(()),

    (Type::Struct(_), SymContainer::Vec(_))
    | (Type::StructInstantiation(_, _), SymContainer::Vec(_)) => Ok(()),

    (Type::Reference(_), _) | (Type::MutableReference(_), _) | (Type::TyParam(_), _) => Err(
      PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
        .with_message(format!("invalid type param for vector: {:?}", ty)),
    ),

    (Type::U8, _)
    | (Type::U64, _)
    | (Type::U128, _)
    | (Type::Bool, _)
    | (Type::Address, _)
    | (Type::Signer, _)
    | (Type::Vector(_), _)
    | (Type::Struct(_), _)
    | (Type::StructInstantiation(_, _), _) => Err(
      PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
        "vector elem layout mismatch, expected {:?}, got {:?}",
        ty, v
      )),
    ),
  }
}

impl<'ctx> SymVectorRef<'ctx> {
  pub fn len(
    &self,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymValue<'ctx>> {
    use SymContainer::*;

    let c = self.0.container();
    check_elem_layout(context, type_param, c)?;

    let len = match c {
      VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r)
      | Vec(r) => r.borrow().symlen(),

      Locals(_) | Struct(_) => unreachable!(),
    };
    Ok(SymValue::from_sym_u64(SymU64::from_ast(len)))
  }

  pub fn push_back(
    &self,
    e: SymValue<'ctx>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<()> {
    use SymContainer::*;

    let c = self.0.container();
    check_elem_layout(context, type_param, c)?;

    match c {
      VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r)
      | Vec(r) => r.borrow_mut().push(&e.as_ast()?),

      Locals(_) | Struct(_) => unreachable!(),
    }
    self.0.mark_dirty();

    Ok(())
  }

  pub fn borrow_elem(
    &self,
    idx: SymU64<'ctx>,
    cost: InternalGasUnits<GasCarrier>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    let c = self.0.container();
    check_elem_layout(context, type_param, c)?;
    // if idx >= c.len() {
    //   return Ok(NativeResult::err(cost, INDEX_OUT_OF_BOUNDS));
    // }
    let idx = SymbolicContainerIndex::Symbolic(idx);
    Ok(SymNativeResult::ok(
      cost,
      vec![SymValue(self.0.borrow_elem(idx)?)],
    ))
  }

  pub fn pop(
    &self,
    cost: InternalGasUnits<GasCarrier>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    use SymContainer::*;

    let c = self.0.container();
    check_elem_layout(context, type_param, c)?;
    // if idx >= c.len() {
    //   return Ok(NativeResult::err(cost, INDEX_OUT_OF_BOUNDS));
    // }
    let (res, vector) = match c {
      VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r)
      | Vec(r) => (r.borrow_mut().pop(), r.borrow()),
      
      Locals(_) | Struct(_) => unreachable!(),
    };
    self.0.mark_dirty();

    Ok(SymNativeResult::ok(
      cost,
      vec![SymValue::from_ast_with_type(
        context.get_z3_ctx(),
        res, &vector.element_type,
      )?],
    ))
  }

  pub fn swap(
    &self,
    idx1: SymU64<'ctx>,
    idx2: SymU64<'ctx>,
    cost: InternalGasUnits<GasCarrier>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    use SymContainer::*;

    let c = self.0.container();
    check_elem_layout(context, type_param, c)?;

    match c {
      VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r)
      | Vec(r) => r.borrow_mut().swap(&idx1, &idx2),

      Locals(_) | Struct(_) => unreachable!(),
    }

    self.0.mark_dirty();

    Ok(SymNativeResult::ok(
      cost,
      vec![],
    ))
  }
}

impl<'ctx> SymVector<'ctx> {
  pub fn empty(
    cost: InternalGasUnits<GasCarrier>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    let z3_ctx = context.get_z3_ctx();
    let container = match type_param {
      Type::U8 => SymValue::from_sym_vec_u8(SymVectorImpl::empty(z3_ctx, &TypeTag::U8)),
      Type::U64 => SymValue::from_sym_vec_u64(SymVectorImpl::empty(z3_ctx, &TypeTag::U64)),
      Type::U128 => SymValue::from_sym_vec_u128(SymVectorImpl::empty(z3_ctx, &TypeTag::U128)),
      Type::Bool => SymValue::from_sym_vec_bool(SymVectorImpl::empty(z3_ctx, &TypeTag::Bool)),
      Type::Address => SymValue::from_sym_vec_address(SymVectorImpl::empty(z3_ctx, &TypeTag::Address)),

      Type::Signer | Type::Vector(_) | Type::Struct(_) | Type::StructInstantiation(_, _) => {
        SymValue(SymValueImpl::Container(SymContainer::Vec(Rc::new(RefCell::new(
          SymVectorImpl::empty(
            z3_ctx,
            &context.type_to_type_tag(type_param)?.ok_or(
              PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
                .with_message(format!("no type tag for type {:?}", type_param)),
            )?),
        )))))
      }

      Type::Reference(_) | Type::MutableReference(_) | Type::TyParam(_) => {
        return Err(
          PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message(format!("invalid type param for vector: {:?}", type_param)),
        )
      }
    };
    Ok(SymNativeResult::ok(cost, vec![container]))
  }

  pub fn destory_empty(
    self,
    cost: InternalGasUnits<GasCarrier>,
    type_param: &Type,
    context: &impl SymNativeContext<'ctx>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    check_elem_layout(context, type_param, &self.0)?;

    // TODO: always assume empty, check in plugin
    Ok(SymNativeResult::ok(cost, vec![]))
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
    // use SymContainer::*;

    match &self {
      // TODO: figure it out
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
    REFERENCE_SIZE
  }
}

impl<'ctx> SymIndexedRef<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    REFERENCE_SIZE
  }
}

impl<'ctx> SymValueImpl<'ctx> {
  fn size(&self) -> AbstractMemorySize<GasCarrier> {
    use SymValueImpl::*;

    match self {
      Invalid | U8(_) | U64(_) | U128(_) | Bool(_) => CONST_SIZE,
      Address(_) => AbstractMemorySize::new(SymAccountAddress::LENGTH as u64),
      ContainerRef(r) => r.size(),
      IndexedRef(r) => r.size(),
      // TODO: in case the borrow fails the VM will panic.
      Container(c) => c.size(),
    }
  }
}

// impl<'ctx> SymStruct<'ctx> {
//   pub fn size(&self) -> AbstractMemorySize<GasCarrier> {
//     self.0.size()
//   }
// }

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
    // REVIEW: this doesn't seem quite right. Consider changing it to
    // a constant positive size or better, something proportional to the size of the value.
    match &self.0 {
      SymGlobalValueImpl::Fresh { .. } | SymGlobalValueImpl::Cached { .. } => REFERENCE_SIZE,
      SymGlobalValueImpl::Deleted | SymGlobalValueImpl::None => MIN_EXISTS_DATA_SIZE,
    }
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
  pub fn pack<I: IntoIterator<Item = SymValue<'ctx>>>(
    z3_ctx: &'ctx Context,
    ty: &StructTag,
    vals: I
  ) -> PartialVMResult<Self> {
    Ok(Self(SymStructImpl::pack(z3_ctx, ty, vals)?))
  }

  pub fn unpack(self) -> PartialVMResult<impl Iterator<Item = SymValue<'ctx>>> {
    Ok(self.0.unpack()?.into_iter())
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
**************************************************************************************/#[allow(clippy::unnecessary_wraps)]
impl<'ctx> SymGlobalValueImpl<'ctx> {
  fn cached(val: SymValueImpl<'ctx>, status: GlobalDataStatus) -> PartialVMResult<Self> {
    match val {
      SymValueImpl::Container(resource) => {
        let status = Rc::new(RefCell::new(status));
        Ok(Self::Cached { resource, status })
      }
      _ => Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("failed to publish cached: not a resource".to_string()),
      ),
    }
  }

  fn fresh(val: SymValueImpl<'ctx>) -> PartialVMResult<Self> {
      match val {
        SymValueImpl::Container(resource) => Ok(Self::Fresh { resource }),
        _ => Err(
          PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message("failed to publish fresh: not a resource".to_string()),
        ),
      }
  }

  fn move_from(&mut self) -> PartialVMResult<SymValueImpl<'ctx>> {
    let resource = match self {
      Self::None | Self::Deleted => {
        return Err(PartialVMError::new(StatusCode::MISSING_DATA))
      }
      Self::Fresh { .. } => match std::mem::replace(self, Self::None) {
        Self::Fresh { resource } => resource,
        _ => unreachable!(),
      },
      Self::Cached { .. } => match std::mem::replace(self, Self::Deleted) {
        Self::Cached { resource, .. } => resource,
        _ => unreachable!(),
      },
    };
    if resource.rc_count() != 1 {
      return Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("moving global resource with dangling reference".to_string()),
      );
    }
    Ok(SymValueImpl::Container(resource))
  }

  fn move_to(&mut self, val: SymValueImpl<'ctx>) -> PartialVMResult<()> {
    match self {
      Self::Fresh { .. } | Self::Cached { .. } => {
        return Err(PartialVMError::new(StatusCode::RESOURCE_ALREADY_EXISTS))
      }
      Self::None => *self = Self::fresh(val)?,
      Self::Deleted => *self = Self::cached(val, GlobalDataStatus::Dirty)?,
    }
    Ok(())
  }

  fn exists(&self) -> PartialVMResult<bool> {
    match self {
      Self::Fresh { .. } | Self::Cached { .. } => Ok(true),
      Self::None | Self::Deleted => Ok(false),
    }
  }

  fn borrow_global(&self) -> PartialVMResult<SymValueImpl<'ctx>> {
    match self {
      Self::None | Self::Deleted => Err(PartialVMError::new(StatusCode::MISSING_DATA)),
      Self::Fresh { resource } => Ok(SymValueImpl::ContainerRef(SymContainerRef::Local {
        container: resource.copy_by_ref(),
        location: SymContainerRefLocation::Independent,
      })),
      Self::Cached { resource, status } => Ok(SymValueImpl::ContainerRef(SymContainerRef::Global {
        container: resource.copy_by_ref(),
        location: SymContainerRefLocation::Independent,
        status: Rc::clone(status),
      })),
    }
  }

  fn into_effect(self) -> PartialVMResult<SymGlobalValueEffect<SymValueImpl<'ctx>>> {
    Ok(match self {
      Self::None => SymGlobalValueEffect::None,
      Self::Deleted => SymGlobalValueEffect::Deleted,
      Self::Fresh { resource } => {
        SymGlobalValueEffect::Changed(SymValueImpl::Container(resource))
      }
      Self::Cached { resource, status } => match &*status.borrow() {
        GlobalDataStatus::Dirty => {
          SymGlobalValueEffect::Changed(SymValueImpl::Container(resource))
        }
        GlobalDataStatus::Clean => SymGlobalValueEffect::None,
      },
    })
  }

  fn is_mutated(&self) -> bool {
    match self {
      Self::None => false,
      Self::Deleted => true,
      Self::Fresh { resource: _ } => true,
      Self::Cached { resource: _, status } => match &*status.borrow() {
        GlobalDataStatus::Dirty => true,
        GlobalDataStatus::Clean => false,
      },
    }
  }

  fn clone_for_symbolic_state_fork(&self) -> Self {
    match self {
      SymGlobalValueImpl::None => SymGlobalValueImpl::None,
      SymGlobalValueImpl::Fresh { resource } => SymGlobalValueImpl::Fresh {
        // Only Locals will fail copy_value(), which is impossible in global value
        resource: resource.copy_value().unwrap(),
      },
      SymGlobalValueImpl::Cached { resource, status } => SymGlobalValueImpl::Cached {
        resource: resource.copy_value().unwrap(),
        status: Rc::new(RefCell::new(status.borrow().clone())),
      },
      SymGlobalValueImpl::Deleted => SymGlobalValueImpl::Deleted,
    }
  }
}

impl<'ctx> SymGlobalValue<'ctx> {
  pub fn none() -> Self {
    Self(SymGlobalValueImpl::None)
  }

  pub fn cached(val: SymValue<'ctx>) -> PartialVMResult<Self> {
    Ok(Self(SymGlobalValueImpl::cached(
      val.0,
      GlobalDataStatus::Clean,
    )?))
  }

  pub fn move_from(&mut self) -> PartialVMResult<SymValue<'ctx>> {
    Ok(SymValue(self.0.move_from()?))
  }

  pub fn move_to(&mut self, val: SymValue<'ctx>) -> PartialVMResult<()> {
    self.0.move_to(val.0)
  }

  pub fn borrow_global(&self) -> PartialVMResult<SymValue<'ctx>> {
    Ok(SymValue(self.0.borrow_global()?))
  }

  pub fn exists(&self) -> PartialVMResult<bool> {
    self.0.exists()
  }

  pub fn into_effect(self) -> PartialVMResult<SymGlobalValueEffect<SymValue<'ctx>>> {
    Ok(match self.0.into_effect()? {
      SymGlobalValueEffect::None => SymGlobalValueEffect::None,
      SymGlobalValueEffect::Deleted => SymGlobalValueEffect::Deleted,
      SymGlobalValueEffect::Changed(v) => SymGlobalValueEffect::Changed(SymValue(v)),
    })
  }

  pub fn is_mutated(&self) -> bool {
    self.0.is_mutated()
  }
  
  pub fn clone_for_symbolic_state_fork(&self) -> Self {
    Self(self.0.clone_for_symbolic_state_fork())
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

      Self::Container(r) => write!(f, "SymContainer({})", r),

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
    use SymContainerRefLocation::*;

    // TODO: this could panic.
    match self {
      Self::Local { container, location } => {
        let loc = match location {
          Dependent { idx, loc } => format!(" @ {}<{:?}>", loc.as_ref(), idx),
          Independent => "".to_string(),
        };
        write!(f, "({}, {}{})", container.rc_count(), container, loc)
      },
      Self::Global { status, container, location } => {
        let loc = match location {
          Dependent { idx, loc } => format!(" @ {}<{:?}>", loc.as_ref(), idx),
          Independent => "".to_string(),
        };
        write!(
          f,
          "({:?}, {}, {}{})",
          &*status.borrow(),
          container.rc_count(),
          container,
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
      Locals(r) => display_list_of_items(r.borrow().iter(), f),
      Struct(r) => write!(f, "{:?}", r),
      Vec(r)
      | VecU8(r)
      | VecU64(r)
      | VecU128(r)
      | VecBool(r)
      | VecAddress(r) => write!(f, "{:?}", r),
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
    write!(
      f,
      "{}",
      self.0
        .borrow()
        .iter()
        .enumerate()
        .map(|(idx, val)| format!("[{}] {}", idx, val))
        .collect::<Vec<_>>()
        .join("\n")
    )
  }
}

/***************************************************************************************
*
* Constants
*
*   Implementation of deseserialization of constant data into a runtime value
*
**************************************************************************************/

impl<'ctx> SymValue<'ctx> {
  fn constant_sig_token_to_layout(constant_signature: &SignatureToken) -> Option<MoveTypeLayout> {
    use MoveTypeLayout as T;
    use SignatureToken as S;

    Some(match constant_signature {
      S::Bool => T::Bool,
      S::U8 => T::U8,
      S::U64 => T::U64,
      S::U128 => T::U128,
      S::Address => T::Address,
      S::Signer => return None,
      S::Vector(inner) => T::Vector(Box::new(Self::constant_sig_token_to_layout(inner)?)),
      // Not yet supported
      S::Struct(_) | S::StructInstantiation(_, _) => return None,
      // Not allowed/Not meaningful
      S::TypeParameter(_) | S::Reference(_) | S::MutableReference(_) => return None,
    })
  }

  fn constant_sig_token_to_tag(constant_signature: &SignatureToken) -> Option<TypeTag> {
    use TypeTag as T;
    use SignatureToken as S;

    Some(match constant_signature {
      S::Bool => T::Bool,
      S::U8 => T::U8,
      S::U64 => T::U64,
      S::U128 => T::U128,
      S::Address => T::Address,
      S::Signer => return None,
      S::Vector(inner) => T::Vector(Box::new(Self::constant_sig_token_to_tag(inner)?)),
      // Not yet supported
      S::Struct(_) | S::StructInstantiation(_, _) => return None,
      // Not allowed/Not meaningful
      S::TypeParameter(_) | S::Reference(_) | S::MutableReference(_) => return None,
    })
  }

  pub fn deserialize_constant(z3_ctx: &'ctx Context, constant: &Constant) -> Option<SymValue<'ctx>> {
    let layout = Self::constant_sig_token_to_layout(&constant.type_)?;
    let tag = Self::constant_sig_token_to_tag(&constant.type_)?;
    let v = Value::simple_deserialize(&constant.data, &layout)?;
    SymValue::from_deserialized_value(z3_ctx, v, &tag).ok()
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

impl<'ctx> SymbolicMoveValue<'ctx> for SymStructImpl<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.data))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymVectorImpl<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.data))
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymContainer<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    use SymContainer::*;

    match &self {
      Locals(_) => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
      Struct(r) => Ok(r.borrow().as_ast()?),
      Vec(r) | VecU8(r) | VecU64(r) | VecU128(r) | VecBool(r) | VecAddress(r) => {
        Ok(r.borrow().as_ast()?)
      }
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymValueImpl<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    use SymValueImpl::*;
  
    match self {
      Invalid => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
    
      U8(v) => Ok(v.as_ast()?),
      U64(v) => Ok(v.as_ast()?),
      U128(v) => Ok(v.as_ast()?),
      Bool(v) => Ok(v.as_ast()?),
      Address(v) => Ok(v.as_ast()?),
    
      Container(c) => Ok(c.as_ast()?),
    
      ContainerRef(_) => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
      IndexedRef(_) => Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR).with_message(format!("{:?} can not be made into ast!", self))),
    }
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymValue<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(self.0.as_ast()?)
  }
}