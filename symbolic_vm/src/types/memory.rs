use move_core_types::{
  identifier::Identifier,
  language_storage::{StructTag, TypeTag},
  value::{MoveStructLayout, MoveTypeLayout},
};
use diem_types::account_address::AccountAddress;

use crate::{
  runtime::context::TypeContext,
  types::{
    values::{
      SymGlobalValue,
      types::{SymStructTag, SymTypeTag},
    },
  },
};

use z3::{
  ast::{Array, BV, Datatype, Dynamic},
  Context,
  DatatypeSort,
};

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
    addr: AccountAddress,
    ty: &StructTag,
  ) -> PartialVMResult<&mut SymGlobalValue<'ctx>> {
    // 1. build SymStructTag
    let tag = SymStructTag::from_struct_tag(z3_ctx, ty_ctx, ty).to_ast().into();
    // 2. build SymMemoryKey
    let ksort = ty_ctx.memory_key_sort();
    let addr_ast = address_to_ast(z3_ctx, addr).into();
    let key = ksort.variants[0].constructor.apply(&[
      &addr_ast,
      &tag,
    ]).as_datatype().unwrap();
    // 3. get_raw -> Datatype
    let val = self.get_raw(&key);
    // 4. Datatype to SymGlobleValue
    let val = ast_to_global_value(val);
    // 5. handle the write back stuff !review this!
    val
  }
}

fn address_to_ast<'ctx>(z3_ctx: &'ctx Context, address: AccountAddress) -> BV<'ctx> {
  let value = u128::from_ne_bytes(address.into());
  BV::from_u64(z3_ctx, (value >> 64) as u64, 64)
    .concat(&BV::from_u64(z3_ctx, value as u64, 64))
}

// TODO: Consider to fork instead of presuppose concrete status
fn test_global_value_variant<'ctx>(sort: &DatatypeSort<'ctx>, ast: &Datatype<'ctx>, idx: usize) -> bool {
  sort.variants[idx].tester.apply(&[&Dynamic::from_ast(ast)]).as_bool().unwrap().as_bool()
    .expect("Global value status should always be concrete")
}

fn ast_to_global_value<'ctx>(ast: Datatype<'ctx>) -> SymGlobalValue<'ctx> {
  // 
}
