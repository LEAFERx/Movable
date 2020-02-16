use libra_types::{identifier::IdentStr, language_storage::ModuleId};
use vm::{errors::VMResult};
use vm_cache_map::Arena;
use vm_runtime::{
  chain_state::ChainState,
  loaded_data::loaded_module::LoadedModule,
};

use crate::{
  engine::solver::Solver,
  symbolic_vm::runtime::SymVMRuntime,
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
      runtime.execute_function(
        self.solver,
        chain_state,
        module,
        function_name,
      )
    })
  }
}
