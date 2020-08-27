use libra_types::{
  vm_error::{
    StatusCode,
    VMStatus,
  },
};
use move_vm_types::{
  // gas_schedule::NativeCostIndex,
  loaded_data::types::{FatStructType, FatType},
  // natives::function::native_gas,
};
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
  pub(super) struct_type: FatStructType,
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
      data: self.data.translate(self.context),
    }
  }

  pub(super) fn equals(&self, other: &Self) -> Bool<'ctx> {
    if self.struct_type.module != other.struct_type.module || self.struct_type.name != other.struct_type.name {
      return Bool::from_bool(self.context, false);
    }
    self.data._eq(&other.data)
  }

  pub(super) fn get_raw(&self, idx: usize) -> VMResult<Dynamic<'ctx>> {
    if idx > self.len() {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("cannot access invalid value at index {}", idx))
      );
    }
    Ok(self.datatype.borrow().variants[0].accessors[idx].apply(&[&Dynamic::from_ast(&self.data)]))
  }

  pub(super) fn set_raw(&mut self, idx: usize, val: Dynamic<'ctx>) -> VMResult<()>{
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
    struct_type: FatStructType,
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
    struct_type: &FatStructType,
    values: I
  ) -> VMResult<Self> {
    let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
    for (idx, field) in struct_type.layout.iter().enumerate() {
      field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
    }
    let field_sort_refs = field_sorts.iter().map(|(idx, field)| (idx.as_str(), field)).collect::<Vec<_>>();
    let datatype = DatatypeBuilder::new(context)
      .variant("Data", field_sort_refs.as_slice())
      .finish(struct_type.struct_tag()?.to_string());
    let fields: VMResult<Vec<_>> = values.into_iter().map(|v| v.as_ast()).collect();
    let fields = fields?;
    let field_refs = fields.iter().collect::<Vec<_>>();
    Ok(Self::new(
      context,
      struct_type.clone(),
      datatype,
      field_refs.as_slice(),
    ))
  }

  fn get_internal(&self, idx: usize) -> VMResult<SymValue<'ctx>> {
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.layout[idx];
    Ok(SymValue::from_ast_with_type_info(self.context, ast, ty)?)
  }

  pub(super) fn unpack(self) -> VMResult<Vec<SymValue<'ctx>>> {
    let mut values = vec![];
    for idx in 0..self.struct_type.layout.len() {
      values.push(self.get_internal(idx)?);
    }
    Ok(values)
  }

  pub(super) fn from_ast(context: &'ctx Context, struct_type: &FatStructType, ast: Datatype<'ctx>) -> VMResult<Self> {
    let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
    for (idx, field) in struct_type.layout.iter().enumerate() {
      field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
    }
    let field_sort_refs = field_sorts.iter().map(|(idx, field)| (idx.as_str(), field)).collect::<Vec<_>>();
    let datatype = DatatypeBuilder::new(context)
      .variant("Data", field_sort_refs.as_slice())
      .finish(struct_type.struct_tag()?.to_string());

    Ok(Self {
      context,
      struct_type: struct_type.clone(),
      datatype: Rc::new(RefCell::new(datatype)),
      data: ast,
    })
  }

  pub(super) fn get(&self, idx: &SymbolicContainerIndex<'ctx>) -> VMResult<SymValue<'ctx>> {
    let idx = idx.to_concrete().ok_or(
      VMStatus::new(StatusCode::INVALID_DATA)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    let ast = self.get_raw(idx)?;
    let ty = &self.struct_type.layout[idx];
    Ok(SymValue::from_ast_with_type_info(self.context, ast, ty)?)
  }

  pub(super) fn set(&mut self, idx: &SymbolicContainerIndex<'ctx>, val: SymValue<'ctx>) -> VMResult<()> {
    let idx = idx.to_concrete().ok_or(
      VMStatus::new(StatusCode::INVALID_DATA)
        .with_message(format!("Symbolic index {:?} cannot be used on Struct", idx))
    )?;
    self.set_raw(idx, val.as_ast()?)?;
    Ok(())
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymStructImpl<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.data))
  }
}

pub(super) fn fat_type_to_sort<'ctx>(context: &'ctx Context, ty: &FatType) -> VMResult<Sort<'ctx>> {
  match ty {
    FatType::Bool => Ok(Sort::bool(context)),
    FatType::U8 => Ok(Sort::bitvector(context, 8)),
    FatType::U64 => Ok(Sort::bitvector(context, 64)),
    FatType::U128 => Ok(Sort::bitvector(context, 128)),
    FatType::Address => Ok(Sort::bitvector(context, 128)),
    FatType::Signer => Ok(Sort::bitvector(context, 128)),
    FatType::Vector(v) => Ok(fat_type_vector_to_sort(context, v)?),
    FatType::Struct(s) => Ok(fat_struct_type_to_sort(context, s)?),
    _ => Err(VMStatus::new(StatusCode::TYPE_ERROR).with_message(format!("{:?} can not be made into a sort!", ty))),
  }
}

pub(super) fn fat_type_vector_to_sort<'ctx>(context: &'ctx Context, ty: &FatType) -> VMResult<Sort<'ctx>> {
  let element_sort = fat_type_to_sort(context, ty)?;
  let sort = DatatypeBuilder::new(context)
    .variant("Vector", &[("array", &element_sort), ("length", &Sort::bitvector(context, 64))])
    .finish(format!("Vector<{}>", ty.type_tag()?))
    .sort;
  Ok(sort)
}

pub(super) fn fat_struct_type_to_sort<'ctx>(context: &'ctx Context, ty: &FatStructType) -> VMResult<Sort<'ctx>> {
  let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
  for (idx, field) in ty.layout.iter().enumerate() {
    field_sorts.push((idx.to_string(), fat_type_to_sort(context, field)?));
  }
  let field_sort_refs = field_sorts.iter().map(|(idx, field)| (idx.as_str(), field)).collect::<Vec<_>>();
  let sort = DatatypeBuilder::new(context)
    .variant("Data", field_sort_refs.as_slice())
    .finish(ty.struct_tag()?.to_string())
    .sort;
  Ok(sort)
}