use move_core_types::{
  language_storage::TypeTag,
};
use vm::errors::*;

use crate::{
  runtime::context::TypeContext,
  types::{
    values::{
      SymAccountAddress,
      SymValue,
      SymGlobalValue,
      types::SymTypeTag,
    },
  },
};

use z3::{
  ast::{Ast, Array, Bool, Datatype, Dynamic},
  Context,
  DatatypeSort,
};

#[derive(Debug)]
pub struct SymLoadResourceResults<'ctx> {
  pub none: (Bool<'ctx>, SymGlobalValue<'ctx>),
  pub fresh: (Bool<'ctx>, SymGlobalValue<'ctx>),
  pub cached: (Bool<'ctx>, SymGlobalValue<'ctx>),
  pub dirty: (Bool<'ctx>, SymGlobalValue<'ctx>),
  pub deleted: (Bool<'ctx>, SymGlobalValue<'ctx>),
}

#[derive(Debug)]
pub struct SymMemory<'ctx> {
  ast: Array<'ctx>,
}

impl<'ctx> SymMemory<'ctx> {
  pub fn new(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>) -> Self {
    Self {
      ast: Array::new_const(z3_ctx, "SymMemory", &ty_ctx.memory_key_sort().sort, &ty_ctx.global_value_sort().sort),
    }
  }

  pub fn fork(&self) -> Self {
    Self { ast: self.ast.clone() }
  }

  pub fn into_simplified_ast(self) -> Array<'ctx> {
    self.ast.simplify()
  }

  fn get_raw(&self, key: &Datatype<'ctx>) -> Datatype<'ctx> {
    self.ast.select(key).as_datatype().unwrap()
  }

  fn set_raw(&mut self, key: &Datatype<'ctx>, val: Datatype<'ctx>) {
    self.ast = self.ast.store(key, &val);
  }

  pub fn load_resource(
    &self,
    z3_ctx: &'ctx Context,
    ty_ctx: &TypeContext<'ctx>, 
    addr: SymAccountAddress<'ctx>,
    ty: TypeTag,
  ) -> PartialVMResult<SymLoadResourceResults<'ctx>> {
    // 1. build SymTypeTag
    let tag = SymTypeTag::from_type_tag(z3_ctx, ty_ctx, &ty).to_ast();
    // 2. build SymMemoryKey
    let ksort = ty_ctx.memory_key_sort();
    let addr_ast = addr.as_inner();
    let key = ksort.variants[0].constructor.apply(&[
      addr_ast,
      &tag,
    ]).as_datatype().unwrap();
    // 3. get_raw -> Datatype
    let val = self.get_raw(&key);
    // 4. Datatype to SymGlobleValue
    global_value_ast_to_global_value(ty_ctx, val, addr, ty)
  }

  pub fn write_resource(
    &mut self,
    z3_ctx: &'ctx Context,
    ty_ctx: &TypeContext<'ctx>,
    val: &SymGlobalValue<'ctx>,
  ) -> PartialVMResult<()> {
    let ty = val.ty();
    let tag_ast = SymTypeTag::from_type_tag(z3_ctx, ty_ctx, ty).to_ast();
    let ksort = ty_ctx.memory_key_sort();
    let addr_ast = val.address().as_inner();
    let key = ksort.variants[0].constructor.apply(&[
      addr_ast,
      &tag_ast,
    ]).as_datatype().unwrap();
    let val = val.as_global_ast(ty_ctx, ty);
    self.set_raw(&key, val);
    Ok(())
  }
}

// TODO: Consider to fork instead of presuppose concrete status
fn global_value_variant_condition<'ctx>(sort: &DatatypeSort<'ctx>, ast: &Datatype<'ctx>, idx: usize) -> Bool<'ctx> {
  sort.variants[idx].tester.apply(&[&Dynamic::from_ast(ast)]).as_bool().unwrap()
}

fn global_value_ast_to_global_value<'ctx>(
  ty_ctx: &TypeContext<'ctx>,
  ast: Datatype<'ctx>,
  addr: SymAccountAddress<'ctx>,
  ty: TypeTag,
) -> PartialVMResult<SymLoadResourceResults<'ctx>> {
  let sort = &ty_ctx.global_value_sort();
  let none = (
    global_value_variant_condition(sort, &ast, 0),
    SymGlobalValue::none(addr.clone(), ty.clone()),
  );
  let fresh = (
    global_value_variant_condition(sort, &ast, 1),
    {
      let ast = sort.variants[1].accessors[0].apply(&[&ast]);
      let val = SymValue::from_runtime_ast_with_type(ty_ctx.z3_ctx(), ty_ctx, ast, &ty)?;
      SymGlobalValue::fresh(addr.clone(), ty.clone(), val)?
    },
  );
  let cached = (
    global_value_variant_condition(sort, &ast, 2),
    {
      let ast = sort.variants[2].accessors[0].apply(&[&ast]);
      let val = SymValue::from_runtime_ast_with_type(ty_ctx.z3_ctx(), ty_ctx, ast, &ty)?;
      SymGlobalValue::cached(addr.clone(), ty.clone(), val)?
    },
  );
  let dirty = (
    global_value_variant_condition(sort, &ast, 3),
    {
      let ast = sort.variants[3].accessors[0].apply(&[&ast]);
      let val = SymValue::from_runtime_ast_with_type(ty_ctx.z3_ctx(), ty_ctx, ast, &ty)?;
      SymGlobalValue::cached_dirty(addr.clone(), ty.clone(), val)?
    },
  );
  let deleted = (
    global_value_variant_condition(sort, &ast, 4),
    SymGlobalValue::deleted(addr, ty),
  );
  Ok(SymLoadResourceResults { none, fresh, cached, dirty, deleted })
}
