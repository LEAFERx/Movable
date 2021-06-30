use move_core_types::{
  identifier::Identifier,
  language_storage::{StructTag, TypeTag},
  value::{MoveStructLayout, MoveTypeLayout},
};
use diem_types::account_address::AccountAddress;

use std::{
  cell::RefCell,
  collections::{HashMap, hash_map::Entry},
  rc::Rc,
};

use z3::{
  ast::Datatype,
  Context as Z3Context,
  datatype_builder::create_datatypes,
  DatatypeAccessor,
  DatatypeBuilder,
  DatatypeSort,
  Sort,
};

#[derive(Debug)]
pub struct TypeContext<'ctx> {
  z3_ctx: &'ctx Z3Context,

  signer_tag: StructTag,
  signer_sort: Rc<DatatypeSort<'ctx>>,

  type_tag_sort: Rc<DatatypeSort<'ctx>>,
  type_tag_list_sort: Rc<DatatypeSort<'ctx>>,
  struct_tag_sort: Rc<DatatypeSort<'ctx>>,

  struct_cache: RefCell<HashMap<StructTag, Rc<DatatypeSort<'ctx>>>>,
  vec_cache: RefCell<HashMap<TypeTag, Rc<DatatypeSort<'ctx>>>>,
  type_cache: RefCell<HashMap<TypeTag, Rc<Sort<'ctx>>>>,
}

impl<'ctx> TypeContext<'ctx> {
  pub fn new(z3_ctx: &'ctx Z3Context) -> Self {
    let mut tag_sorts = type_tag_datatype_sorts(z3_ctx);
    Self {
      z3_ctx,
      signer_tag: signer_tag(),
      signer_sort: Rc::new(signer_sort(z3_ctx)),

      type_tag_sort: Rc::new(tag_sorts.remove(0)),
      type_tag_list_sort: Rc::new(tag_sorts.remove(0)),
      struct_tag_sort: Rc::new(tag_sorts.remove(0)),

      struct_cache: RefCell::new(HashMap::new()),
      vec_cache: RefCell::new(HashMap::new()),
      type_cache: RefCell::new(HashMap::new()),
    }
  }

  pub fn signer_tag(&self) -> &StructTag {
    &self.signer_tag
  }

  pub fn signer_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.signer_sort)
  }

  pub fn struct_tag_to_datatype_sort(&self, ty: StructTag) -> Rc<DatatypeSort<'ctx>> {
    match self.struct_cache.borrow_mut().entry(ty) {
      Entry::Occupied(e) => Rc::clone(e.get()),
      Entry::Vacant(e) => Rc::clone({
        let s = Rc::new(struct_tag_to_datatype_sort(self.z3_ctx, e.key()));
        e.insert(s)
      })
    }
  }

  pub fn vec_to_datatype_sort(&self, ty: TypeTag) -> Rc<DatatypeSort<'ctx>> {
    match self.vec_cache.borrow_mut().entry(ty) {
      Entry::Occupied(e) => Rc::clone(e.get()),
      Entry::Vacant(e) => Rc::clone({
        let s = Rc::new(vec_to_datatype_sort(self.z3_ctx, e.key()));
        e.insert(s)
      })
    }
  }

  pub fn type_tag_to_sort(&self, ty: TypeTag) -> Rc<Sort<'ctx>> {
    match self.type_cache.borrow_mut().entry(ty) {
      Entry::Occupied(e) => Rc::clone(e.get()),
      Entry::Vacant(e) => Rc::clone({
        let s = Rc::new(type_tag_to_sort(self.z3_ctx, e.key()));
        e.insert(s)
      })
    }
  }

  pub fn struct_tag_to_layout(&self, ty: &StructTag) -> MoveStructLayout {
    struct_tag_to_layout(ty)
  }

  pub fn type_tag_to_layout(&self, ty: &TypeTag) -> MoveTypeLayout {
    type_tag_to_layout(ty)
  }
}

// Singer

// A fake signer tag
// Should only be used in signer container
// TODO: consider remove this by refactoring SymStructImpl (struct_type field)
fn signer_tag() -> StructTag {
  StructTag {
    address: AccountAddress::from_hex_literal("0x1").unwrap(),
    module: Identifier::new("Signer").unwrap(),
    name: Identifier::new("signer").unwrap(),
    type_params: vec![TypeTag::Address],
  }
}

fn signer_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> DatatypeSort<'ctx> {
  DatatypeBuilder::new(z3_ctx, "signer")
    .variant("signer", vec![("a", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128)))])
    .finish()
}

// TypeTag
fn type_tag_datatype_sorts<'ctx>(z3_ctx: &'ctx Z3Context) -> Vec<DatatypeSort<'ctx>> {
  let t = DatatypeBuilder::new(z3_ctx, "TypeTag")
    .variant("Bool", vec![])
    .variant("U8", vec![])
    .variant("U64", vec![])
    .variant("U128", vec![])
    .variant("Address", vec![])
    .variant("Signer", vec![])
    .variant("Vector", vec![("Vector", DatatypeAccessor::Datatype("TypeTag".into()))])
    .variant("Struct", vec![("Struct", DatatypeAccessor::Datatype("StructTag".into()))]);
  let tl = DatatypeBuilder::new(z3_ctx, "TypeTagList")
    .variant("nil", vec![])
    .variant("item", vec![
      ("val", DatatypeAccessor::Datatype("TypeTag".into())),
      ("next", DatatypeAccessor::Datatype("TypeTagList".into())),
    ]);
  let addr_sort = Sort::bitvector(z3_ctx, 128);
  let str_sort = Sort::string(z3_ctx);
  let int_sort = Sort::int(z3_ctx);
  let s = DatatypeBuilder::new(z3_ctx, "StructTag")
    .variant("StructTag", vec![
      ("address", DatatypeAccessor::Sort(&addr_sort)),
      ("module", DatatypeAccessor::Sort(&str_sort)),
      ("name", DatatypeAccessor::Sort(&str_sort)),
      ("type_params_len", DatatypeAccessor::Sort(&int_sort)),
      ("type_params", DatatypeAccessor::Datatype("TypeTagList".into())),
    ]);
  create_datatypes(vec![t, tl, s])
}

// fn make_memory_key_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> DatatypeSort<'ctx> {
//   let sorts = make_tag_datatype_sorts(z3_ctx);
//   DatatypeBuilder::new(z3_ctx, "SymMemoryKey")
//     .variant("SymMemoryKey", vec![
//       ("Address", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128))),
//       ("Type", DatatypeAccessor::Sort(&sorts[2].sort)),
//     ])
//     .finish()
// }

// fn make_value_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> Vec<DatatypeSort<'ctx>> {
//   let v = DatatypeBuilder::new(z3_ctx, "Value")
//     .variant("Bool", vec![("val", DatatypeAccessor::Sort(&Sort::bool(z3_ctx)))])
//     .variant("U8", vec![("val", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 8)))])
//     .variant("U64", vec![("val", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 64)))])
//     .variant("U128", vec![("val", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128)))])
//     .variant("Address", vec![("val", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128)))])
//     .variant("Vector", vec![
//       ("val", DatatypeAccessor::Datatype("ValueList".into())),
//       ("len", DatatypeAccessor::Sort(&Sort::int(z3_ctx))),
//     ]);
//   let vl = DatatypeBuilder::new(z3_ctx, "ValueList")
//     .variant("nil", vec![])
//     .variant("item", vec![
//       ("val", DatatypeAccessor::Datatype("Value".into())),
//       ("next", DatatypeAccessor::Datatype("ValueList".into())),
//     ]);
//   create_datatypes(vec![v, vl])
// }

// fn make_global_value_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> DatatypeSort<'ctx> {

// }

// fn make_memory_value_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> DatatypeSort<'ctx> {

// }

// fn make_memory_sort<'ctx>(z3_ctx: &'ctx Z3Context) -> Sort<'ctx> {
//   Sort::
// }

// Ultility

fn struct_tag_to_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context, ty: &StructTag) -> DatatypeSort<'ctx> {
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

fn vec_to_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context, ty: &TypeTag) -> DatatypeSort<'ctx> {
  let element_sort = type_tag_to_sort(z3_ctx, ty);
  let array_sort = Sort::array(z3_ctx, &Sort::bitvector(z3_ctx, 64), &element_sort);
  DatatypeBuilder::new(z3_ctx, format!("Vector<{}>", ty))
    .variant("Vector", vec![
      ("array", DatatypeAccessor::Sort(&array_sort)),
      ("length", DatatypeAccessor::Sort(&Sort::bitvector(z3_ctx, 128))),
    ])
    .finish()
}

fn type_tag_to_sort<'ctx>(z3_ctx: &'ctx Z3Context, ty: &TypeTag) -> Sort<'ctx> {
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

fn struct_tag_to_layout(ty: &StructTag) -> MoveStructLayout {
  let layout = ty.type_params.iter().map(|ty| type_tag_to_layout(ty)).collect();
  MoveStructLayout::new(layout)
}

fn type_tag_to_layout(ty: &TypeTag) -> MoveTypeLayout {
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