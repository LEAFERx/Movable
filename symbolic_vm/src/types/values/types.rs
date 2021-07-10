use diem_types::{
  account_address::AccountAddress,
};
use move_core_types::{
  identifier::Identifier,
  language_storage::{StructTag, TypeTag},
};

use crate::{
  runtime::context::TypeContext,
};

use z3::{
  ast::{Ast, BV, Datatype, Dynamic, String as Z3String},
  Context,
  DatatypeSort,
};

pub struct SymTypeTag<'ctx> {
  ast: Datatype<'ctx>,
}

pub struct SymStructTag<'ctx> {
  ast: Datatype<'ctx>,
}

impl<'ctx> SymTypeTag<'ctx> {
  pub fn new(ast: Datatype<'ctx>) -> Self {
    Self { ast }
  }

  pub fn from_type_tag(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, tag: &TypeTag) -> Self {
    Self {
      ast: build_type_tag_ast(z3_ctx, ty_ctx, tag)
    }
  }

  pub fn to_ast(self) -> Datatype<'ctx> {
    self.ast
  }

  pub fn to_type_tag(&self, ty_ctx: &TypeContext<'ctx>) -> TypeTag {
    ast_to_type_tag(ty_ctx, &self.ast)
  }
}

impl<'ctx> SymStructTag<'ctx> {
  pub fn new(ast: Datatype<'ctx>) -> Self {
    Self { ast }
  }

  pub fn from_struct_tag(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, tag: &StructTag) -> Self {
    Self {
      ast: build_struct_tag_ast(z3_ctx, ty_ctx, tag)
    }
  }

  pub fn to_ast(self) -> Datatype<'ctx> {
    self.ast
  }

  pub fn to_struct_tag(&self, ty_ctx: &TypeContext<'ctx>) -> StructTag {
    ast_to_struct_tag(ty_ctx, &self.ast)
  }
}

fn build_type_tag_ast<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, tag: &TypeTag) -> Datatype<'ctx> {
  let sort = ty_ctx.type_tag_sort();
  let ast = match tag {
    TypeTag::Bool => sort.variants[0].constructor.apply(&[]),
    TypeTag::U8 => sort.variants[1].constructor.apply(&[]),
    TypeTag::U64 => sort.variants[2].constructor.apply(&[]),
    TypeTag::U128 => sort.variants[3].constructor.apply(&[]),
    TypeTag::Address => sort.variants[4].constructor.apply(&[]),
    TypeTag::Signer => sort.variants[5].constructor.apply(&[]),
    TypeTag::Vector(vtag) => sort.variants[6].constructor.apply(&[&build_type_tag_ast(z3_ctx, ty_ctx, vtag)]),
    TypeTag::Struct(stag) => sort.variants[7].constructor.apply(&[&build_struct_tag_ast(z3_ctx, ty_ctx, stag)]),
  };
  ast.as_datatype().unwrap()
}

fn build_struct_tag_ast<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, stag: &StructTag) -> Datatype<'ctx> {
  let sort = ty_ctx.struct_tag_sort();
  let addr = u128::from_ne_bytes(stag.address.into());
  let addr_ast = BV::from_u64(z3_ctx, (addr >> 64) as u64, 64)
    .concat(&BV::from_u64(z3_ctx, addr as u64, 64));
  
  let tylist_sort = ty_ctx.type_tag_list_sort();
  let mut types_ast = tylist_sort.variants[0].constructor.apply(&[]);
  for tag in stag.type_params.iter().rev() {
    let tag_ast = build_type_tag_ast(z3_ctx, ty_ctx, tag);
    types_ast = tylist_sort.variants[1].constructor.apply(&[
      &tag_ast,
      &types_ast,
    ]);
  }
  
  sort.variants[0].constructor.apply(&[
    &addr_ast,
    &Z3String::from_str(z3_ctx, stag.module.as_ident_str().as_str()).unwrap(),
    &Z3String::from_str(z3_ctx, stag.name.as_ident_str().as_str()).unwrap(),
    &types_ast,
  ]).as_datatype().unwrap()
}

fn test_type_variant<'ctx>(sort: &DatatypeSort<'ctx>, ast: &Datatype<'ctx>, idx: usize) -> bool {
  sort.variants[idx].tester.apply(&[&Dynamic::from_ast(ast)]).as_bool().unwrap().as_bool()
    .expect("Type should always be concrete")
}

fn ast_to_type_tag<'ctx>(ty_ctx: &TypeContext<'ctx>, ast: &Datatype<'ctx>) -> TypeTag {
  let sort = ty_ctx.type_tag_sort();

  if test_type_variant(&sort, ast, 0) {
    return TypeTag::Bool;
  }
  if test_type_variant(&sort, ast, 1) {
    return TypeTag::U8;
  }
  if test_type_variant(&sort, ast, 2) {
    return TypeTag::U64;
  }
  if test_type_variant(&sort, ast, 3) {
    return TypeTag::U128;
  }
  if test_type_variant(&sort, ast, 4) {
    return TypeTag::Address;
  }
  if test_type_variant(&sort, ast, 5) {
    return TypeTag::Signer;
  }
  if test_type_variant(&sort, ast, 6) {
    let vast = sort.variants[6].accessors[0].apply(&[&Dynamic::from_ast(ast)]).as_datatype().unwrap();
    let vtag = ast_to_type_tag(ty_ctx, &vast);
    return TypeTag::Vector(Box::new(vtag));
  }
  if test_type_variant(&sort, ast, 7) {
    let sast = sort.variants[7].accessors[0].apply(&[&Dynamic::from_ast(ast)]).as_datatype().unwrap();
    let stag = ast_to_struct_tag(ty_ctx, &sast);
    return TypeTag::Struct(stag);
  }
  unreachable!()
}

// The address of the type is always concrete!
fn ast_to_address<'ctx>(ast: &BV<'ctx>) -> AccountAddress {
  let high = ast.extract(127, 64).simplify().as_u64().unwrap();
  let low = ast.extract(63, 0).simplify().as_u64().unwrap();
  let bytes = [high.to_ne_bytes(), low.to_ne_bytes()].concat();
  AccountAddress::from_hex(bytes).unwrap()
}

fn ast_to_struct_tag<'ctx>(ty_ctx: &TypeContext<'ctx>, ast: &Datatype<'ctx>) -> StructTag {
  let tl_sort = ty_ctx.type_tag_list_sort();
  let s_sort = ty_ctx.struct_tag_sort();
  let ast = Dynamic::from_ast(ast);
  let addr_ast = s_sort.variants[0].accessors[0].apply(&[&ast]).as_bv().unwrap();
  let module_ast = s_sort.variants[0].accessors[1].apply(&[&ast]).as_string().unwrap();
  let name_ast = s_sort.variants[0].accessors[2].apply(&[&ast]).as_string().unwrap();
  let len_ast = s_sort.variants[0].accessors[3].apply(&[&ast]).as_int().unwrap();
  let mut types_ast = s_sort.variants[0].accessors[4].apply(&[&ast]).as_datatype().unwrap();
  let address = ast_to_address(&addr_ast);
  let module = module_ast.as_string().unwrap();
  let name = name_ast.as_string().unwrap();
  let len = len_ast.as_u64().unwrap();
  let mut type_params = vec![];
  for _ in 0..len {
    let ty_ast = tl_sort.variants[0].accessors[0].apply(&[&Dynamic::from_ast(&types_ast)]).as_datatype().unwrap();
    type_params.push(ast_to_type_tag(ty_ctx, &ty_ast));
    types_ast = tl_sort.variants[0].accessors[1].apply(&[&Dynamic::from_ast(&types_ast)]).as_datatype().unwrap();
  }
  StructTag {
    address,
    module: Identifier::new(module).unwrap(),
    name: Identifier::new(name).unwrap(),
    type_params,
  }
}
