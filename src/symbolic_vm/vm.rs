use libra_types::{
  identifier::IdentStr,
  language_storage::ModuleId,
  vm_error::{StatusCode, VMStatus},
};
use vm::{
  errors::*,
  file_format::{
    SignatureToken,
  }
};
use vm_cache_map::Arena;
use vm_runtime::{
  chain_state::ChainState,
  loaded_data::{function::{FunctionRef, FunctionReference}, loaded_module::LoadedModule},
};

use crate::{
  engine::solver::Solver,
  symbolic_vm::{
    runtime::SymVMRuntime,
    types::value::SymValue,
  },
};
use symbolic_vm_definition::SymbolicVMImpl;

rental! {
  mod symbolic_vm_definition {
    use super::*;

    #[rental]
    pub struct SymbolicVMImpl<'ctx> {
      alloc: Box<Arena<LoadedModule>>,
      runtime: SymVMRuntime<'ctx, 'alloc>,
    }
  }
}

pub struct SymbolicVM<'ctx> {
  solver: &'ctx Solver<'ctx>,
  vm: SymbolicVMImpl<'ctx>,
}

impl<'ctx> SymbolicVM<'ctx> {
  pub fn new(solver: &'ctx Solver<'ctx>) -> Self {
    SymbolicVM {
      solver,
      vm: SymbolicVMImpl::new(Box::new(Arena::new()), |arena| {
        SymVMRuntime::new(&*arena)
      }),
    }
  }

  pub fn execute_function<S: ChainState>(
    &self,
    module: &ModuleId,
    function_name: &IdentStr,
    // gas_schedule: &CostTable,
    chain_state: &mut S,
    // txn_data: &TransactionMetadata,
  ) -> VMResult<()> {
    self.vm.rent(|runtime| {
      let args = construct_symbolic_args(module, function_name, self.solver, runtime, chain_state)?;
      runtime.execute_function(
        self.solver,
        chain_state,
        module,
        function_name,
        args,
      )
    })
  }
}

//// Construct symbolic arguments
fn construct_symbolic_args<'ctx, S: ChainState>(
  module: &ModuleId,
  function_name: &IdentStr,
  solver: &Solver<'ctx>,
  runtime: &SymVMRuntime<'ctx, '_>,
  chain_state: &mut S,
) -> VMResult<Vec<SymValue<'ctx>>> {
  let loaded_module = runtime.get_loaded_module(module, chain_state)?;
  let func_idx = loaded_module
    .function_defs_table
    .get(function_name)
    .ok_or_else(|| VMStatus::new(StatusCode::LINKER_ERROR))?;
  let func = FunctionRef::new(loaded_module, *func_idx);
  let mut args = vec![];
  let prefix = "TestFuncArgs";
  for sig in func.signature().arg_types.clone() {
    let val = match sig {
      SignatureToken::Bool => SymValue::new_bool(solver, prefix),
      SignatureToken::U8 => SymValue::new_u8(solver, prefix),
      SignatureToken::U64 => SymValue::new_u64(solver, prefix),
      SignatureToken::U128 => SymValue::new_u128(solver, prefix),
      _ => unimplemented!(),
    };
    args.push(val);
  }
  Ok(args)
}