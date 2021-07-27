use diem_types::account_address::AccountAddress;

use language_e2e_tests::data_store::{FakeDataStore, GENESIS_CHANGE_SET};
use move_core_types::{
  gas_schedule::{GasAlgebra, GasUnits},
  identifier::{IdentStr, Identifier},
  language_storage::ModuleId,
};

use serde::{Deserialize, Serialize};
use z3::{
  ast::{Ast, BV, Bool, Dynamic},
  Context,
};

use symbolic_vm::{
  plugin::{IntegerArithmeticPlugin, Plugin, PluginManager, VerificationPlugin},
  runtime::vm::SymbolicVM,
  types::values::{SymValue, VMSymValueCast, SymU64, SymBool},
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

pub struct Engine<'a> {
  data_store: FakeDataStore,
  plugin_manager: PluginManager<'a>,
}

impl<'a> Engine<'a> {
  pub fn from_genesis() -> Self {
    let mut data_store = FakeDataStore::default();
    data_store.add_write_set(GENESIS_CHANGE_SET.clone().write_set());
    Engine {
      data_store,
      plugin_manager: PluginManager::new(),
    }
  }

  pub fn add_module(&mut self, module_id: &ModuleId, blob: Vec<u8>) {
    self.data_store.add_module(module_id, blob);
  }

  pub fn add_plugin(&mut self, plugin: impl Plugin + 'a) {
    self.plugin_manager.add_plugin(plugin)
  }
  
  pub fn execute_function<'ctx>(&mut self, z3_ctx: &'ctx Context, module: &ModuleId, function_name: &IdentStr) {
    let vm = SymbolicVM::new(z3_ctx);
    let sender = AccountAddress::random();
    let session = vm.new_session(&self.data_store);

    session.execute_function(&self.plugin_manager, module, function_name, vec![])
      .expect("VM should run correctly")
  }
}
