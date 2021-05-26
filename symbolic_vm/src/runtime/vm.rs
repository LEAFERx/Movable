use crate::runtime::runtime::VMRuntime;
use move_core_types::{
  // gas_schedule::CostTable,
  identifier::IdentStr,
  language_storage::{ModuleId, TypeTag},};
use diem_vm::{
  transaction_metadata::TransactionMetadata,
};
// use diem_types::{
//   vm_error::{StatusCode, VMStatus},
// };
use vm::{
  errors::PartialVMResult,
  file_format::{
    SignatureToken, CompiledModule,
  },
};

use z3::Context;
use crate::{
  plugin::PluginManager,
  types::values::SymValue,
};

pub struct SymbolicVM<'ctx> {
  runtime: VMRuntime<'ctx>,
  z3_ctx: &'ctx Context,
}

impl<'ctx> SymbolicVM<'ctx> {
  pub fn new(z3_ctx: &'ctx Context) -> Self {
    Self {
      runtime: VMRuntime::new(),
      z3_ctx,
    }
  }

  pub fn execute_function<'vtxn>(
    &self,
    module: &ModuleId,
    function_name: &IdentStr,
    // gas_schedule: &CostTable,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    plugin_manager: &mut PluginManager<'_, 'ctx>,
    // ty_args: Vec<TypeTag>,
    // args: Vec<SymValue<'ctx>>,
  ) -> PartialVMResult<()> {
    let (ty_args, args) = construct_symbolic_args(module, function_name, self.z3_ctx, &self.runtime, vm_ctx)?;
    self.runtime.execute_function(
      self.z3_ctx,
      vm_ctx,
      txn_data,
      plugin_manager,
      // gas_schedule,
      module,
      function_name,
      ty_args,
      args,
    )
  }

  // pub fn execute_script<'vtxn>(
  //   &self,
  //   script: Vec<u8>,
  //   gas_schedule: &CostTable,
  //   vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
  //   txn_data: &'vtxn TransactionMetadata,
  //   ty_args: Vec<TypeTag>,
  //   args: Vec<SymValue<'ctx>>,
  // ) -> PartialVMResult<()> {
  //   self
  //     .runtime
  //     .execute_script(self.context, vm_ctx, txn_data, gas_schedule, script, ty_args, args)
  // }

  pub fn publish_module<'vtxn>(
    &self,
    module: Vec<u8>,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
  ) -> PartialVMResult<()> {
    self.runtime.publish_module(module, vm_ctx, txn_data)
  }

  pub fn cache_module(
    &self,
    module: CompiledModule,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
  ) -> PartialVMResult<()> {
    self.runtime.cache_module(module, vm_ctx)
  }
}

// impl Default for SymbolicVM {
//   fn default() -> Self {
//     Self::new()
//   }
// }

//// Construct symbolic arguments
fn construct_symbolic_args<'ctx>(
  module: &ModuleId,
  function_name: &IdentStr,
  z3_ctx: &'ctx Context,
  runtime: &VMRuntime<'ctx>,
  vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
) -> PartialVMResult<(Vec<TypeTag>, Vec<SymValue<'ctx>>)> {
  let func = runtime.load_function(function_name, module, vm_ctx)?;
  let mut args = vec![];
  let prefix = "TestFuncArgs";
  let mut ty_args = vec![];
  for sig in &func.parameters().0 {
    let (ty, val) = match sig {
      SignatureToken::Bool => (TypeTag::Bool, SymValue::new_bool(z3_ctx, prefix)),
      SignatureToken::U8 => (TypeTag::U8, SymValue::new_u8(z3_ctx, prefix)),
      SignatureToken::U64 => (TypeTag::U64, SymValue::new_u64(z3_ctx, prefix)),
      SignatureToken::U128 => (TypeTag::U128, SymValue::new_u128(z3_ctx, prefix)),
      _ => unimplemented!(),
    };
    args.push(val);
    ty_args.push(ty);
  }
  Ok((ty_args, args))
}