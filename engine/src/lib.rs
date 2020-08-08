use libra_types::account_address::AccountAddress;

use language_e2e_tests::data_store::{FakeDataStore, GENESIS_CHANGE_SET_FRESH};
use move_core_types::{
  gas_schedule::{GasAlgebra, GasUnits},
  identifier::IdentStr,
  language_storage::ModuleId,
};
use move_vm_state::{data_cache::BlockDataCache};
use move_vm_types::transaction_metadata::TransactionMetadata;
use vm::CompiledModule;

use serde::{Deserialize, Serialize};
use z3::{Config, Context};

use z3::Solver;
use symbolic_vm::{
  runtime::vm::SymbolicVM,
  state::vm_context::SymbolicVMContext,
};

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
struct ModuleList {
  address: [u8; AccountAddress::LENGTH],
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
    engine
      .data_store
      .add_write_set(GENESIS_CHANGE_SET_FRESH.clone().write_set());
    engine
  }

  pub fn add_module(&mut self, module_id: &ModuleId, module: &CompiledModule) {
    self.data_store.add_module(module_id, module);
  }
  
  pub fn execute_function(&self, module: &ModuleId, function_name: &IdentStr) {
    let config = Config::new();
    let context = Context::new(&config);
    let solver = Solver::new(&context);
    let vm = SymbolicVM::new(&solver);
    let data_cache = BlockDataCache::new(&self.data_store);
    let mut vm_ctx = SymbolicVMContext::new(&context, GasUnits::new(0), &data_cache);
    vm.execute_function(module, function_name, &mut vm_ctx, &TransactionMetadata::default())
      .expect("VM should run correctly");
  }
}
