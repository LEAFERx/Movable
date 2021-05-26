use move_core_types::{
  identifier::Identifier,
  language_storage::{StructTag, TypeTag},
  value::{MoveStructLayout, MoveTypeLayout},
};
use move_vm_types::loaded_data::runtime_types::{StructType, Type};
use diem_types::account_address::AccountAddress;
use z3::{
  Context,
  DatatypeAccessor,
  DatatypeBuilder,
  DatatypeSort,
  Sort,
};

// A fake signer tag
// Should only be used in signer container
// TODO: consider remove this by refactoring SymStructImpl (struct_type field)
pub fn signer_tag() -> StructTag {
  StructTag {
    address: AccountAddress::from_hex_literal("0x1").unwrap(),
    module: Identifier::new("Signer").unwrap(),
    name: Identifier::new("signer").unwrap(),
    type_params: vec![TypeTag::Address],
  }
}

pub fn signer_sort<'ctx>(z3_ctx: &'ctx Context) -> DatatypeSort<'ctx> {
  DatatypeBuilder::new(z3_ctx, "signer")
    .variant("signer", vec![("a", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128)))])
    .finish()
}

pub fn struct_tag_to_datatype_sort<'ctx>(z3_ctx: &'ctx Context, ty: &StructTag) -> DatatypeSort<'ctx> {
  if ty.name == Identifier::new("signer").unwrap() {
    panic!("Should never use this function on signer!");
    // return signer_sort(z3_ctx);
  }
  let mut field_sorts: Vec<(String, Sort<'ctx>)> = vec![];
  for (idx, field) in ty.type_params.iter().enumerate() {
    field_sorts.push((idx.to_string(), type_tag_to_sort(z3_ctx, field)));
  }
  let field_sort_refs = field_sorts.iter()
    .map(|(idx, field)| (idx.as_str(), DatatypeAccessor::Sort(field))).collect::<Vec<_>>();
  DatatypeBuilder::new(z3_ctx, ty.to_string())
    .variant("Data", field_sort_refs)
    .finish()
}

pub fn vec_to_datatype_sort<'ctx>(z3_ctx: &'ctx Context, ty: &TypeTag) -> DatatypeSort<'ctx> {
  let element_sort = type_tag_to_sort(z3_ctx, ty);
  let array_sort = Sort::array(z3_ctx, &Sort::bitvector(z3_ctx, 64), &element_sort);
  DatatypeBuilder::new(z3_ctx, format!("Vector<{}>", ty))
    .variant("Vector", vec![
      ("array", DatatypeAccessor::Sort(&array_sort)),
      ("length", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128))),
    ])
    .finish()
}

pub fn type_tag_to_sort<'ctx>(z3_ctx: &'ctx Context, ty: &TypeTag) -> Sort<'ctx> {
  use TypeTag::*;
  match ty {
    Bool => Sort::bool(z3_ctx),
    U8 => Sort::bitvector(z3_ctx, 8),
    U64 => Sort::bitvector(z3_ctx, 64),
    U128 => Sort::bitvector(z3_ctx, 128),
    Address => Sort::bitvector(z3_ctx, 128),
    Signer => signer_sort(z3_ctx).sort,
    Vector(ty) => vec_to_datatype_sort(z3_ctx, ty).sort,
    Struct(ty) => struct_tag_to_datatype_sort(z3_ctx, ty).sort,
  }
}

pub fn struct_tag_to_layout(ty: &StructTag) -> MoveStructLayout {
  let layout = ty.type_params.iter().map(|ty| type_tag_to_layout(ty)).collect();
  MoveStructLayout::new(layout)
}

pub fn type_tag_to_layout(ty: &TypeTag) -> MoveTypeLayout {
  use TypeTag as T;
  use MoveTypeLayout as M;

  match ty {
    T::Bool => M::Bool,
    T::U8 => M::U8,
    T::U64 => M::U64,
    T::U128 => M::U128,
    T::Address => M::Address,
    T::Signer => M::Signer,
    T::Vector(ty) => M::Vector(Box::new(type_tag_to_layout(ty))),
    T::Struct(ty) => M::Struct(struct_tag_to_layout(ty)),
  }
}
