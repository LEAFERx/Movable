use move_vm_runtime::{
  data_cache::RemoteCache,
};
use move_vm_types::loaded_data::runtime_types::Type;
use move_core_types::{
  account_address::AccountAddress,
  identifier::IdentStr,
  language_storage::{ModuleId, TypeTag},
};
use vm::errors::*;
use vm::file_format::SignatureToken;
use z3::Context;

use crate::{
  plugin::{
    PluginManager,
  },
  runtime::{
    context::TypeContext,
    data_cache::SymDataCache,
    runtime::VMRuntime,
  },
  types::{
    values::{SymValue, SymLocals},
  },
};

pub struct Session<'ctx, 'r, 'l, R> {
  pub(crate) z3_ctx: &'ctx Context,
  pub(crate) runtime: &'l VMRuntime<'ctx>,
  pub(crate) data_cache: SymDataCache<'ctx, 'r, 'l, R>,
}

impl<'ctx, 'r, 'l, R: RemoteCache> Session<'ctx, 'r, 'l, R> {
  pub fn execute_function(
    mut self,
    plugin_manager: &PluginManager<'_>,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: Vec<TypeTag>,
  ) -> VMResult<()> {
    let (_ref_locals, args) = self.construct_symbolic_args(
      self.runtime.ty_ctx(),
      module,
      function_name,
      &ty_args,
    )?;
    self.runtime.execute_function(
      self.z3_ctx,
      plugin_manager,
      module,
      function_name,
      ty_args,
      args,
      self.data_cache
    )
  }

  pub fn publish_module(
    &mut self,
    module: Vec<u8>,
    sender: AccountAddress,
  ) -> VMResult<()> {
    self.runtime.publish_module(
      module,
      sender,
      &mut self.data_cache,
    )
  }

  fn type_tag_to_new_sym_value(
    &self,
    ty_ctx: &TypeContext<'ctx>,
    tag: TypeTag,
    prefix: &str,
  ) -> SymValue<'ctx> {
    let z3_ctx = self.z3_ctx;
    match tag {
      TypeTag::Bool => SymValue::new_bool(z3_ctx, prefix),
      TypeTag::U8 => SymValue::new_u8(z3_ctx, prefix),
      TypeTag::U64 => SymValue::new_u64(z3_ctx, prefix),
      TypeTag::U128 => SymValue::new_u128(z3_ctx, prefix),
      TypeTag::Address => SymValue::new_address(z3_ctx, prefix),
      TypeTag::Signer => SymValue::new_signer(z3_ctx, ty_ctx, prefix),
      TypeTag::Vector(vtag) => SymValue::new_vector(z3_ctx, ty_ctx, prefix, vtag.as_ref().clone()),
      TypeTag::Struct(_) => SymValue::new_struct(z3_ctx, ty_ctx, prefix, tag.clone()),
    }
  }

  fn construct_symbolic_args(
    &mut self,
    ty_ctx: &TypeContext<'ctx>,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: &[TypeTag],
  ) -> VMResult<(SymLocals<'ctx>, Vec<SymValue<'ctx>>)> {
    let z3_ctx = self.z3_ctx;
    let (_, _, parameter_tys, _) = self.runtime.load_function(
      module,
      function_name,
      ty_args,
      &mut self.data_cache,
    )?;
    let mut args = vec![];
    let prefix = "TestFuncArgs";
    let mut num_refs = 0;
    for ty in &parameter_tys {
      match ty {
        Type::Reference(_) | Type::MutableReference(_) => { num_refs += 1; },
        _ => {},
      }
    }
    let mut ref_idx = 0;
    let mut ref_locals = SymLocals::new(z3_ctx, num_refs);
    for ty in parameter_tys {
      match ty {
        Type::Reference(ty) | Type::MutableReference(ty) => {
          let tag = self.runtime.type_to_type_tag(&ty);
          let val = match tag {
            Ok(tag) => self.type_tag_to_new_sym_value(ty_ctx, tag, prefix),
            Err(_) => unimplemented!(), // Can not handle multi-level reference now
          };
          ref_locals.store_loc(ref_idx, val).unwrap();
          args.push(ref_locals.borrow_loc(ref_idx).unwrap());
          ref_idx += 1;
        },
        _ => {
          let tag = self.runtime.type_to_type_tag(&ty);
          let val = match tag {
            Ok(tag) => self.type_tag_to_new_sym_value(ty_ctx, tag, prefix),
            Err(_) => unimplemented!(), // Can not type reference other than reference or primitives now
          };
          args.push(val);
        }
      }
    }
    Ok((ref_locals, args))
  }
}