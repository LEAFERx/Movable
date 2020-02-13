use libra_types::{
  account_address::ADDRESS_LENGTH,
  identifier::IdentStr,
  language_storage::ModuleId,
};
use language_e2e_tests::{
  data_store::{
    FakeDataStore,
    GENESIS_WRITE_SET,
  },

};
use vm::{
  CompiledModule,
  gas_schedule::{
    GasUnits,
    GasAlgebra,
  },
};
use vm_runtime::{
  data_cache::BlockDataCache,
  chain_state::TransactionExecutionContext,
};

use z3::{
  Config,
  Context,
};
use serde::{Serialize, Deserialize};

use crate::symbolic_vm::{
  vm::SymbolicVM,
};

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
struct ModuleList {
  address: [u8; ADDRESS_LENGTH],
  modules: Vec<String>,
}

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct EngineConfig {
  module_list: Vec<ModuleList>,
}

pub struct Engine {
  data_store: FakeDataStore,
}

impl Engine {
  pub fn from_genesis() -> Self {
    let mut engine = Engine {
      data_store: FakeDataStore::default(),
    };
    engine.data_store.add_write_set(&GENESIS_WRITE_SET);
    engine
  }

  pub fn add_module(&mut self, module_id: &ModuleId, module: &CompiledModule) {
    self.data_store.add_module(module_id, module);
  }

  pub fn execute_function(&self, module: &ModuleId, function_name: &IdentStr) {
    let config = Config::new();
    let context = Context::new(&config);
    let vm = SymbolicVM::new(&context);
    let data_cache = BlockDataCache::new(&self.data_store);
    let mut interp_context = TransactionExecutionContext::new(GasUnits::new(0), &data_cache);
    vm.execute_function(module, function_name, &mut interp_context).expect("VM should run correctly");
  }
}