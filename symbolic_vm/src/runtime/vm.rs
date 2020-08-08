use crate::runtime::runtime::VMRuntime;
use bytecode_verifier::VerifiedModule;
use move_core_types::{
  gas_schedule::CostTable,
  identifier::IdentStr,
  language_storage::{ModuleId, TypeTag},};
use move_vm_types::{
  transaction_metadata::TransactionMetadata,
};
use crate::state::vm_context::SymbolicVMContext;
// use libra_types::{
//   vm_error::{StatusCode, VMStatus},
// };
use vm::{
  errors::VMResult,
  file_format::{
    SignatureToken,
  },
};

use z3::Solver;
use crate::types::values::SymValue;

pub struct SymbolicVM<'ctx> {
  runtime: VMRuntime<'ctx>,
  solver: &'ctx Solver<'ctx>,
}

impl<'ctx> SymbolicVM<'ctx> {
  pub fn new(solver: &'ctx Solver<'ctx>) -> Self {
    Self {
      runtime: VMRuntime::new(),
      solver,
    }
  }

  pub fn execute_function<'vtxn>(
    &self,
    module: &ModuleId,
    function_name: &IdentStr,
    // gas_schedule: &CostTable,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    // ty_args: Vec<TypeTag>,
    // args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let args = construct_symbolic_args(module, function_name, self.solver, &self.runtime, vm_ctx)?;
    self.runtime.execute_function(
      self.solver,
      vm_ctx,
      txn_data,
      // gas_schedule,
      module,
      function_name,
      // ty_args,
      args,
    )
  }

  pub fn execute_script<'vtxn>(
    &self,
    script: Vec<u8>,
    gas_schedule: &CostTable,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    ty_args: Vec<TypeTag>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    self
      .runtime
      .execute_script(self.solver, vm_ctx, txn_data, gas_schedule, script, ty_args, args)
  }

  pub fn publish_module<'vtxn>(
    &self,
    module: Vec<u8>,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
  ) -> VMResult<()> {
    self.runtime.publish_module(module, vm_ctx, txn_data)
  }

  pub fn cache_module(
    &self,
    module: VerifiedModule,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
  ) -> VMResult<()> {
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
  solver: &'ctx Solver<'ctx>,
  runtime: &VMRuntime<'ctx>,
  vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
) -> VMResult<Vec<SymValue<'ctx>>> {
  let func = runtime.load_function(function_name, module, vm_ctx)?;
  let mut args = vec![];
  let prefix = "TestFuncArgs";
  for sig in func.parameters().0.clone() {
    let val = match sig {
      SignatureToken::Bool => SymValue::new_bool(solver.get_context(), prefix),
      SignatureToken::U8 => SymValue::new_u8(solver.get_context(), prefix),
      SignatureToken::U64 => SymValue::new_u64(solver.get_context(), prefix),
      SignatureToken::U128 => SymValue::new_u128(solver.get_context(), prefix),
      _ => unimplemented!(),
    };
    args.push(val);
  }
  Ok(args)
}