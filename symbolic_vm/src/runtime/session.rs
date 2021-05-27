use move_vm_runtime::{
  data_cache::RemoteCache,
};

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
    data_cache::SymDataCache,
    runtime::VMRuntime,
  },
  types::{
    values::SymValue,
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
    plugin_manager: &mut PluginManager<'_, 'ctx>,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: Vec<TypeTag>,
  ) -> VMResult<()> {
    let args = self.construct_symbolic_args(
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

  fn construct_symbolic_args(
    &mut self,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: &[TypeTag],
  ) -> VMResult<Vec<SymValue<'ctx>>> {
    let z3_ctx = self.z3_ctx;
    let (func, _, _, _) = self.runtime.load_function(
      module,
      function_name,
      ty_args,
      &mut self.data_cache,
    )?;
    let mut args = vec![];
    let prefix = "TestFuncArgs";
    for sig in &func.parameters().0 {
      let val = match sig {
        SignatureToken::Bool => SymValue::new_bool(z3_ctx, prefix),
        SignatureToken::U8 => SymValue::new_u8(z3_ctx, prefix),
        SignatureToken::U64 => SymValue::new_u64(z3_ctx, prefix),
        SignatureToken::U128 => SymValue::new_u128(z3_ctx, prefix),
        _ => unimplemented!(),
      };
      args.push(val);
    }
    Ok(args)
  }
}