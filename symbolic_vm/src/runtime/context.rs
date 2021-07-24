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
  ast::{Ast, Bool, BV, Datatype, Dynamic},
  Context as Z3Context,
  datatype_builder::create_datatypes,
  DatatypeAccessor,
  DatatypeBuilder,
  DatatypeSort,
  RecFuncDecl,
  Sort,
  SortKind,
  Symbol,
};

#[derive(Debug)]
pub struct ValueListFunctionDecls<'ctx> {
  pub empty: Rc<RecFuncDecl<'ctx>>,
  pub len: Rc<RecFuncDecl<'ctx>>,
  pub select: Rc<RecFuncDecl<'ctx>>,
  pub store: Rc<RecFuncDecl<'ctx>>,
  pub push: Rc<RecFuncDecl<'ctx>>,
  pub pop_vl: Rc<RecFuncDecl<'ctx>>,
  pub pop_res: Rc<RecFuncDecl<'ctx>>,
}

#[derive(Debug)]
pub struct TypeContext<'ctx> {
  z3_ctx: &'ctx Z3Context,

  signer_tag: StructTag,
  signer_sort: Rc<DatatypeSort<'ctx>>,

  type_tag_sort: Rc<DatatypeSort<'ctx>>,
  type_tag_list_sort: Rc<DatatypeSort<'ctx>>,
  struct_tag_sort: Rc<DatatypeSort<'ctx>>,

  value_sort: Rc<DatatypeSort<'ctx>>,
  value_list_sort: Rc<DatatypeSort<'ctx>>,
  value_list_function_decls: Rc<ValueListFunctionDecls<'ctx>>,
  global_value_sort: Rc<DatatypeSort<'ctx>>,

  memory_key_sort: Rc<DatatypeSort<'ctx>>,
  memory_sort: Rc<Sort<'ctx>>,

  // struct_cache: RefCell<HashMap<StructTag, Rc<DatatypeSort<'ctx>>>>,
  // vec_cache: RefCell<HashMap<TypeTag, Rc<DatatypeSort<'ctx>>>>,
  // vec_func_cache: RefCell<HashMap<TypeTag, Rc<VectorFunctionDecls<'ctx>>>>,
  type_cache: RefCell<HashMap<TypeTag, Rc<Sort<'ctx>>>>,
}

impl<'ctx> TypeContext<'ctx> {
  pub fn new(z3_ctx: &'ctx Z3Context) -> Self {
    let mut tag_sorts = type_tag_datatype_sorts(z3_ctx);
    let type_tag_sort = tag_sorts.remove(0);
    let type_tag_list_sort = tag_sorts.remove(0);
    let struct_tag_sort = tag_sorts.remove(0);

    let mut value_sorts = value_datatype_sorts(z3_ctx);
    let value_sort = value_sorts.remove(0);
    let value_list_sort = value_sorts.remove(0);
    let value_list_function_decls = value_list_function_decls(z3_ctx, &value_list_sort, &value_sort.sort);
    let global_value_sort = global_value_datatype_sort(z3_ctx, &value_list_sort.sort);

    let memory_key_sort = memory_key_datatype_sort(z3_ctx, &type_tag_sort.sort);
    let memory_sort = memory_sort(z3_ctx, &memory_key_sort.sort, &global_value_sort.sort);

    Self {
      z3_ctx,
      signer_tag: signer_tag(),
      signer_sort: Rc::new(signer_sort(z3_ctx)),

      type_tag_sort: Rc::new(type_tag_sort),
      type_tag_list_sort: Rc::new(type_tag_list_sort),
      struct_tag_sort: Rc::new(struct_tag_sort),
      
      value_sort: Rc::new(value_sort),
      value_list_sort: Rc::new(value_list_sort),
      value_list_function_decls: Rc::new(value_list_function_decls),

      global_value_sort: Rc::new(global_value_sort),

      memory_key_sort: Rc::new(memory_key_sort),
      memory_sort: Rc::new(memory_sort),

      // struct_cache: RefCell::new(HashMap::new()),
      // vec_cache: RefCell::new(HashMap::new()),
      // vec_func_cache: RefCell::new(HashMap::new()),
      type_cache: RefCell::new(HashMap::new()),
    }
  }

  pub fn z3_ctx(&self) -> &'ctx Z3Context {
    self.z3_ctx
  }

  pub fn signer_tag(&self) -> &StructTag {
    &self.signer_tag
  }

  pub fn signer_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.signer_sort)
  }

  pub fn type_tag_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.type_tag_sort)
  }

  pub fn type_tag_list_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.type_tag_list_sort)
  }

  pub fn struct_tag_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.struct_tag_sort)
  }

  pub fn value_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.value_sort)
  }

  pub fn value_list_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.value_list_sort)
  }

  pub fn value_list_function_decls(&self) -> Rc<ValueListFunctionDecls<'ctx>> {
    Rc::clone(&self.value_list_function_decls)
  }

  pub fn global_value_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.global_value_sort)
  }

  pub fn memory_key_sort(&self) -> Rc<DatatypeSort<'ctx>> {
    Rc::clone(&self.memory_key_sort)
  }

  pub fn memory_sort(&self) -> Rc<Sort<'ctx>> {
    Rc::clone(&self.memory_sort)
  }

  // pub fn struct_tag_to_datatype_sort(&self, ty: StructTag) -> Rc<DatatypeSort<'ctx>> {
  //   match self.struct_cache.borrow_mut().entry(ty) {
  //     Entry::Occupied(e) => Rc::clone(e.get()),
  //     Entry::Vacant(e) => Rc::clone({
  //       let s = Rc::new(struct_tag_to_datatype_sort(self.z3_ctx, e.key()));
  //       e.insert(s)
  //     })
  //   }
  // }

  // pub fn vec_to_datatype_sort(&self, ty: TypeTag) -> Rc<DatatypeSort<'ctx>> {
  //   match self.vec_cache.borrow_mut().entry(ty) {
  //     Entry::Occupied(e) => Rc::clone(e.get()),
  //     Entry::Vacant(e) => Rc::clone({
  //       let s = Rc::new(vec_to_datatype_sort(self.z3_ctx, e.key()));
  //       e.insert(s)
  //     })
  //   }
  // }

  // pub fn vec_func_decls(&self, ty: TypeTag) -> Rc<VectorFunctionDecls<'ctx>> {
  //   let vsort = self.vec_to_datatype_sort(ty.clone());
  //   match self.vec_func_cache.borrow_mut().entry(ty) {
  //     Entry::Occupied(e) => Rc::clone(e.get()),
  //     Entry::Vacant(e) => Rc::clone({
  //       let s = Rc::new(vector_function_decls(
  //         self.z3_ctx, &type_tag_to_sort(self.z3_ctx, e.key()), &vsort));
  //       e.insert(s)
  //     })
  //   }
  // }

  pub fn value_ast_to_runtime_ast(&self, ast: Dynamic<'ctx>, ty: &TypeTag) -> Dynamic<'ctx> {
    match ty {
      TypeTag::Bool => self.value_sort.variants[0].accessors[0].apply(&[&ast]),
      TypeTag::U8 => self.value_sort.variants[1].accessors[0].apply(&[&ast]),
      TypeTag::U64 => self.value_sort.variants[2].accessors[0].apply(&[&ast]),
      TypeTag::U128 => self.value_sort.variants[3].accessors[0].apply(&[&ast]),
      TypeTag::Address => self.value_sort.variants[4].accessors[0].apply(&[&ast]),
      // This returns a ValueList!
      TypeTag::Signer
      | TypeTag::Vector(_)
      | TypeTag::Struct(_) => self.value_sort.variants[5].accessors[0].apply(&[&ast]),
    }
  }

  pub fn runtime_ast_to_value_ast(&self, ast: Dynamic<'ctx>, ty: &TypeTag) -> Dynamic<'ctx> {
    match ty {
      TypeTag::Bool => self.value_sort.variants[0].constructor.apply(&[&ast]),
      TypeTag::U8 => self.value_sort.variants[1].constructor.apply(&[&ast]),
      TypeTag::U64 => self.value_sort.variants[2].constructor.apply(&[&ast]),
      TypeTag::U128 => self.value_sort.variants[3].constructor.apply(&[&ast]),
      TypeTag::Address => self.value_sort.variants[4].constructor.apply(&[&ast]),
      // `ast` should be a ValueList!
      TypeTag::Signer
      | TypeTag::Vector(_)
      | TypeTag::Struct(_) => self.value_sort.variants[5].constructor.apply(&[&ast]),
    }
  }

  pub fn fresh_value_const(&self, ty: &TypeTag, prefix: &str) -> Dynamic<'ctx> {
    fresh_value_const(self.z3_ctx, self, ty, prefix)
  }

  pub fn fresh_value_list_const(&self, ty: &TypeTag, prefix: &str) -> Option<Dynamic<'ctx>> {
    fresh_value_list_const(self.z3_ctx, self, ty, prefix)
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
    .variant("signer", vec![("a", DatatypeAccessor::Sort(Sort::bitvector(z3_ctx, 128)))])
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
      ("address", DatatypeAccessor::Sort(addr_sort)),
      ("module", DatatypeAccessor::Sort(str_sort.clone())),
      ("name", DatatypeAccessor::Sort(str_sort)),
      // ("type_params_len", DatatypeAccessor::Sort(int_sort)),
      ("type_params", DatatypeAccessor::Datatype("TypeTagList".into())),
    ]);
  create_datatypes(vec![t, tl, s])
}

// Value
fn value_datatype_sorts<'ctx>(z3_ctx: &'ctx Z3Context) -> Vec<DatatypeSort<'ctx>> {
  let bool_ = Sort::bool(z3_ctx);
  let u8_ = Sort::bitvector(z3_ctx, 8);
  let u64_ = Sort::bitvector(z3_ctx, 64);
  let u128_ = Sort::bitvector(z3_ctx, 128);
  let int = Sort::int(z3_ctx);
  let v = DatatypeBuilder::new(z3_ctx, "Value")
    .variant("Bool", vec![("val", DatatypeAccessor::Sort(bool_))])
    .variant("U8", vec![("val", DatatypeAccessor::Sort(u8_))])
    .variant("U64", vec![("val", DatatypeAccessor::Sort(u64_))])
    .variant("U128", vec![("val", DatatypeAccessor::Sort(u128_.clone()))])
    .variant("Address", vec![("val", DatatypeAccessor::Sort(u128_))])
    .variant("ValueList", vec![
      ("val", DatatypeAccessor::Datatype("ValueList".into())),
    ]);
  let vl = DatatypeBuilder::new(z3_ctx, "ValueList")
    .variant("nil", vec![])
    .variant("item", vec![
      ("val", DatatypeAccessor::Datatype("Value".into())),
      ("next", DatatypeAccessor::Datatype("ValueList".into())),
    ]);
  create_datatypes(vec![v, vl])
}

fn global_value_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context, value_list_sort: &Sort<'ctx>) -> DatatypeSort<'ctx> {
  DatatypeBuilder::new(z3_ctx, "SymGlobalValue")
    .variant("None", vec![])
    .variant("Fresh", vec![("value", DatatypeAccessor::Sort(value_list_sort.clone()))])
    .variant("CachedClean", vec![("value", DatatypeAccessor::Sort(value_list_sort.clone()))])
    .variant("CachedDirty", vec![("value", DatatypeAccessor::Sort(value_list_sort.clone()))])
    .variant("Deleted", vec![])
    .finish()
}

fn memory_key_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context, ty_sort: &Sort<'ctx>) -> DatatypeSort<'ctx> {
  DatatypeBuilder::new(z3_ctx, "SymMemoryKey")
    .variant("SymMemoryKey", vec![
      ("Address", DatatypeAccessor::Sort(Sort::bitvector(z3_ctx, 128))),
      ("Type", DatatypeAccessor::Sort(ty_sort.clone())),
    ])
    .finish()
}

fn memory_sort<'ctx>(z3_ctx: &'ctx Z3Context, key_sort: &Sort<'ctx>, val_sort: &Sort<'ctx>) -> Sort<'ctx> {
  Sort::array(z3_ctx, key_sort, val_sort)
}

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
    .map(|(idx, field)| (idx.as_str(), DatatypeAccessor::Sort(field.clone()))).collect::<Vec<_>>();
  DatatypeBuilder::new(z3_ctx, ty.to_string())
    .variant("Data", field_sort_refs)
    .finish()
}

fn vec_to_datatype_sort<'ctx>(z3_ctx: &'ctx Z3Context, ty: &TypeTag) -> DatatypeSort<'ctx> {
  let element_sort = type_tag_to_sort(z3_ctx, ty);
  DatatypeBuilder::new(z3_ctx, format!("Vector<{}>", ty))
    .variant("VectorNil", vec![])
    .variant("VectorCons", vec![
      ("value", DatatypeAccessor::Sort(element_sort)),
      ("next", DatatypeAccessor::Datatype(Symbol::String(format!("Vector<{}>", ty)))),
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

// For `vector_function_decls` only
fn sort_to_new_const<'ctx>(z3_ctx: &'ctx Z3Context, sort: &Sort<'ctx>, name: &str) -> Dynamic<'ctx> {
  match sort.kind() {
    SortKind::Bool => Bool::new_const(z3_ctx, name).into(),
    SortKind::BV => BV::new_const(z3_ctx, name, 64).into(),
    SortKind::Datatype => Datatype::new_const(z3_ctx, name, sort).into(),
    _ => unreachable!(),
  }
}

fn value_list_function_decls<'ctx>(z3_ctx: &'ctx Z3Context, vlsort: &DatatypeSort<'ctx>, vsort: &Sort<'ctx>) -> ValueListFunctionDecls<'ctx> {
  let zero = Dynamic::from_ast(&BV::from_u64(z3_ctx, 0, 64));
  let nil = vlsort.variants[0].constructor.apply(&[]);
  let v = Datatype::new_const(z3_ctx, "ValueListArg", &vlsort.sort).into();
  let idx = BV::new_const(z3_ctx, "IndexArg", 64).into();
  let elem = sort_to_new_const(z3_ctx, vsort, "ValueArg");

  let empty = RecFuncDecl::new(z3_ctx, "ValueListEmpty", &[&vlsort.sort], &Sort::bool(z3_ctx));
  empty.add_def(&[&v], &v._eq(&nil));
  
  let len = RecFuncDecl::new(z3_ctx, "ValueListLen", &[&vlsort.sort], &Sort::bitvector(z3_ctx, 64));
  len.add_def(&[&v], &v._eq(&nil).ite(
    &zero,
    &Dynamic::from(len.apply(&[&vlsort.variants[1].accessors[1].apply(&[&v])]).as_bv().unwrap() + 1u64),
  ));
  
  let select = RecFuncDecl::new(z3_ctx, "ValueListSelect", &[&vlsort.sort, &Sort::bitvector(z3_ctx, 64)], vsort);
  select.add_def(&[&v, &idx], &idx._eq(&zero).ite(
    &vlsort.variants[1].accessors[0].apply(&[&v]),
    &select.apply(&[
      &vlsort.variants[1].accessors[1].apply(&[&v]),
      &Dynamic::from(idx.as_bv().unwrap() - 1u64)
    ]),
  ));
  
  let store = RecFuncDecl::new(z3_ctx, "ValueListStore", &[&vlsort.sort, &Sort::bitvector(z3_ctx, 64), &vsort], &vlsort.sort);
  store.add_def(&[&v, &idx, &elem], &idx._eq(&zero).ite(
    &vlsort.variants[1].constructor.apply(&[&elem, &v]),
    &vlsort.variants[1].constructor.apply(&[
      &vlsort.variants[1].accessors[0].apply(&[&v]),
      &store.apply(&[
        &vlsort.variants[1].accessors[1].apply(&[&v]),
        &Dynamic::from(idx.as_bv().unwrap() - 1u64),
        &elem,
      ]),
    ]),
  ));
  
  let push = RecFuncDecl::new(z3_ctx, "ValueListPush", &[&vlsort.sort, vsort], &vlsort.sort);
  push.add_def(&[&v, &elem], &v._eq(&nil).ite(
    &vlsort.variants[1].constructor.apply(&[&elem, &nil]),
    &vlsort.variants[1].constructor.apply(&[
      &vlsort.variants[1].accessors[0].apply(&[&v]),
      &push.apply(&[
        &vlsort.variants[1].accessors[1].apply(&[&v]),
        &elem,
      ]),
    ]),
  ));
  
  let pop_vl = RecFuncDecl::new(z3_ctx, "ValueListPop[ValueList]", &[&vlsort.sort], &vlsort.sort);
  pop_vl.add_def(&[&v], &nil._eq(
    &vlsort.variants[1].accessors[1].apply(&[&v]),
  ).ite(
    &nil,
    &vlsort.variants[1].constructor.apply(&[
      &vlsort.variants[1].accessors[0].apply(&[&v]),
      &pop_vl.apply(&[&vlsort.variants[1].accessors[1].apply(&[&v])]),
    ]),
  ));
  
  let pop_res = RecFuncDecl::new(z3_ctx, "ValueListPop[ValueResult]", &[&vlsort.sort], &vsort);
  pop_res.add_def(&[&v], &nil._eq(
    &vlsort.variants[1].accessors[1].apply(&[&v]),
  ).ite(
    &vlsort.variants[1].accessors[0].apply(&[&v]),
    &pop_res.apply(&[&vlsort.variants[1].accessors[1].apply(&[&v])]),
  ));

  ValueListFunctionDecls {
    empty: Rc::new(empty),
    len: Rc::new(len),
    select: Rc::new(select),
    store: Rc::new(store),
    push: Rc::new(push),
    pop_vl: Rc::new(pop_vl),
    pop_res: Rc::new(pop_res),
  }
}

fn fresh_value_const<'ctx>(
  z3_ctx: &'ctx Z3Context,
  ty_ctx: &TypeContext<'ctx>,
  ty: &TypeTag,
  prefix: &str,
) -> Dynamic<'ctx> {
  let vsort = ty_ctx.value_sort();
  let vlsort = ty_ctx.value_list_sort();

  match ty {
    TypeTag::Bool => vsort.variants[0].constructor.apply(&[&Bool::fresh_const(z3_ctx, prefix)]),
    TypeTag::U8 => vsort.variants[1].constructor.apply(&[&BV::fresh_const(z3_ctx, prefix, 8)]),
    TypeTag::U64 => vsort.variants[2].constructor.apply(&[&BV::fresh_const(z3_ctx, prefix, 64)]),
    TypeTag::U128 => vsort.variants[3].constructor.apply(&[&BV::fresh_const(z3_ctx, prefix, 128)]),
    TypeTag::Address => vsort.variants[4].constructor.apply(&[&BV::fresh_const(z3_ctx, prefix, 128)]),
    TypeTag::Signer
    | TypeTag::Vector(_)
    | TypeTag::Struct(_) => vsort.variants[5].constructor.apply(&[
      &fresh_value_list_const(z3_ctx, ty_ctx, ty, prefix).unwrap(),
    ]),
  }
}

fn fresh_value_list_const<'ctx>(
  z3_ctx: &'ctx Z3Context,
  ty_ctx: &TypeContext<'ctx>,
  ty: &TypeTag,
  prefix: &str,
) -> Option<Dynamic<'ctx>> {
  let vsort = ty_ctx.value_sort();
  let vlsort = ty_ctx.value_list_sort();

  Some(match ty {
    TypeTag::Signer => vlsort.variants[1].constructor.apply(&[
      // Address
      &vsort.variants[4].constructor.apply(&[&BV::fresh_const(z3_ctx, prefix, 128)]),
      // Nil
      &vlsort.variants[0].constructor.apply(&[]),
    ]),
    TypeTag::Vector(ty) => {
      // TODO: There is no good way to constraint all value in value list to be the same type with dynamic list size
      // TODO: Maybe add constraints to solver?
      Datatype::fresh_const(z3_ctx, prefix, &vlsort.sort).into()
    },
    TypeTag::Struct(stag) => {
      let mut data = vlsort.variants[0].constructor.apply(&[]); // ValueListNil
      let mut i = stag.type_params.len();
      for ty in stag.type_params.iter().rev() {
        data = vlsort.variants[1].constructor.apply(&[
          &fresh_value_const(z3_ctx, ty_ctx, ty, &format!("{}.{}", prefix, i)),
          &data,
        ]);
        i = i - 1;
      }
      data
    },
    _ => return None,
  })
}
