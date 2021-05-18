use move_core_types::{
  value::{
    MoveStructLayout, MoveTypeLayout,
  },
  vm_status::{
    StatusCode, VMStatus,
  },
};
// use move_vm_types::{
//   gas_schedule::NativeCostIndex,
//   natives::function::native_gas,
// };
use std::{
  cell::RefCell,
  fmt::Debug,
  rc::Rc,
};
use vm::{
  errors::*,
};

use z3::{
  ast::{Ast, Datatype, Dynamic, Bool},
  Context,
  DatatypeAccessor,
  DatatypeBuilder,
  DatatypeSort,
  Sort,
};

use crate::types::{
  values::{
    values_impl::{SymValue, SymbolicContainerIndex},
    SymbolicMoveValue,
  },
};

/// A Z3 datatype wrapper for Move struct
#[derive(Debug)]
pub(super) struct SymStructImpl<'ctx> {
  pub(super) context: &'ctx Context,
  pub(super) struct_type: MoveStructLayout,
  pub(super) datatype: Rc<RefCell<DatatypeSort<'ctx>>>,
  pub(super) data: Datatype<'ctx>,
}

impl<'ctx> SymStructImpl<'ctx> {
  pub(super) fn len(&self) -> usize {
    self.datatype.borrow().variants[0].accessors.len()
  }

  pub(super) fn copy_value(&self) -> Self {
    Self {
      context: self.context,
      struct_type: self.struct_type.clone(),
      datatype: Rc::clone(&self.datatype),
      data: self.data.clone(),
    }
  }

  pub(super) fn equals(&self, other: &Self) -> Bool<'ctx> {
    if self.struct_type.module != other.struct_type.module || self.struct_type.name != other.struct_type.name {
      return Bool::from_bool(self.context, false);
    }
    self.data._eq(&other.data)
  }

  pub(super) fn get_raw(&self, idx: usize) -> PartialVMResult<Dynamic<'ctx>> {
    if idx > self.len() {
      return Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot access invalid value at index {}", idx))
      );
    }
    Ok(self.datatype.borrow().variants[0].accessors[idx].apply(&[&Dynamic::from_ast(&self.data)]))
  }

  pub(super) fn set_raw(&mut self, idx: usize, val: Dynamic<'ctx>) -> PartialVMResult<()>{
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

  fn new(
    context: &'ctx Context,
    struct_type: MoveStructLayout,
    datatype: DatatypeSort<'ctx>,
    fields: &[&Dynamic<'ctx>]
  ) -> Self {
    let datatype = Rc::new(RefCell::new(datatype));
    let data = datatype.borrow().variants[0].constructor.apply(fields).as_datatype().unwrap();
    Self {
      context,
      struct_type,
      datatype,
      data,
    }
  }

  pub(super) fn pack<I: IntoIterator<Item = SymValue<'ctx>>>(
    context: &'ctx Context,
    struct_type: &MoveStructLayout,
    values: I
  ) -> PartialVMResult<Self> {
    let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
    for (idx, field) in struct_type.layout.iter().enumerate() {
      field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
    }
    let field_sort_refs = field_sorts.iter()
      .map(|(idx, field)| (idx.as_str(), DatatypeAccessor::Sort(field))).collect::<Vec<_>>();
    let datatype = DatatypeBuilder::new(context, struct_type.struct_tag()?.to_string())
      .variant("Data", field_sort_refs)
      .finish();
    let fields: PartialVMResult<Vec<_>> = values.into_iter().map(|v| v.as_ast()).collect();
    let fields = fields?;
    let field_refs = fields.iter().collect::<Vec<_>>();
    Ok(Self::new(
      context,
      struct_type.clone(),
      datatype,
      field_refs.as_slice(),
    ))
  }

  fn get_internal(&self, idx: usize) -> PartialVMResult<SymValue<'ctx>> {
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.layout[idx];
    Ok(SymValue::from_ast_with_type(self.context, ast, ty)?)
  }

  pub(super) fn unpack(self) -> PartialVMResult<Vec<SymValue<'ctx>>> {
    let mut values = vec![];
    for idx in 0..self.struct_type.layout.len() {
      values.push(self.get_internal(idx)?);
    }
    Ok(values)
  }

  pub(super) fn from_ast(context: &'ctx Context, struct_type: &MoveStructLayout, ast: Datatype<'ctx>) -> PartialVMResult<Self> {
    let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
    for (idx, field) in struct_type.layout.iter().enumerate() {
      field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
    }
    let field_sort_refs = field_sorts.iter()
      .map(|(idx, field)| (idx.as_str(), DatatypeAccessor::Sort(field))).collect::<Vec<_>>();
    let datatype = DatatypeBuilder::new(context, struct_type.struct_tag()?.to_string())
      .variant("Data", field_sort_refs)
      .finish();

    Ok(Self {
      context,
      struct_type: struct_type.clone(),
      datatype: Rc::new(RefCell::new(datatype)),
      data: ast,
    })
  }

  pub(super) fn get(&self, idx: &SymbolicContainerIndex<'ctx>) -> PartialVMResult<SymValue<'ctx>> {
    let idx = idx.to_concrete().ok_or(
      PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.layout[idx];
    Ok(SymValue::from_ast_with_type(self.context, ast, ty)?)
  }

  pub(super) fn set(&mut self, idx: &SymbolicContainerIndex<'ctx>, val: SymValue<'ctx>) -> PartialVMResult<()> {
    let idx = idx.to_concrete().ok_or(
      PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    self.set_raw(idx, val.as_ast()?)?;
    Ok(())
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymStructImpl<'ctx> {
  fn as_ast(&self) -> PartialVMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.data))
  }
}

pub(super) fn fat_type_to_sort<'ctx>(context: &'ctx Context, ty: &MoveTypeLayout) -> PartialVMResult<Sort<'ctx>> {
  match ty {
    MoveTypeLayout::Bool => Ok(Sort::bool(context)),
    MoveTypeLayout::U8 => Ok(Sort::bitvector(context, 8)),
    MoveTypeLayout::U64 => Ok(Sort::bitvector(context, 64)),
    MoveTypeLayout::U128 => Ok(Sort::bitvector(context, 128)),
    MoveTypeLayout::Address => Ok(Sort::bitvector(context, 128)),
    MoveTypeLayout::Signer => Ok(Sort::bitvector(context, 128)),
    MoveTypeLayout::Vector(v) => Ok(fat_type_vector_to_sort(context, v)?),
    MoveTypeLayout::Struct(s) => Ok(fat_struct_type_to_sort(context, s)?),
    _ => Err(PartialVMError::new(StatusCode::UNKNOWN_RUNTIME_STATUS).with_message(format!("{:?} can not be made into a sort!", ty))),
  }
}

pub(super) fn fat_type_vector_to_sort<'ctx>(context: &'ctx Context, ty: &MoveTypeLayout) -> PartialVMResult<Sort<'ctx>> {
  let element_sort = fat_type_to_sort(context, ty)?;
  let array_sort = Sort::array(context, &Sort::bitvector(context, 64), &element_sort);
  let sort = DatatypeBuilder::new(context, format!("Vector<{}>", ty.type_tag()?))
    .variant("Vector",
      vec![
        ("array", DatatypeAccessor::Sort(&array_sort)),
        ("length", DatatypeAccessor::Sort(&Sort::bitvector(context, 64))),
      ])
    .finish()
    .sort;
  Ok(sort)
}

pub(super) fn fat_struct_type_to_sort<'ctx>(context: &'ctx Context, ty: &MoveStructLayout) -> PartialVMResult<Sort<'ctx>> {
  let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
  for (idx, field) in ty.layout.iter().enumerate() {
    field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
  }
  let field_sort_refs = field_sorts.iter()
    .map(|(idx, field)| (idx.as_str(), DatatypeAccessor::Sort(field))).collect::<Vec<_>>();
  let sort = DatatypeBuilder::new(context, ty.struct_tag()?.to_string())
    .variant("Data", field_sort_refs)
    .finish()
    .sort;
  Ok(sort)
}