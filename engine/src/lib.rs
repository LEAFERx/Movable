use diem_types::account_address::AccountAddress;

use language_e2e_tests::data_store::{FakeDataStore, GENESIS_CHANGE_SET};
use move_core_types::{
  gas_schedule::{GasAlgebra, GasUnits},
  identifier::{IdentStr, Identifier},
  language_storage::ModuleId,
};
use diem_vm::data_cache::StateViewCache;
use move_vm_types::transaction_metadata::TransactionMetadata;
use vm::CompiledModule;

use serde::{Deserialize, Serialize};
use z3::{Config, Context, ast::{Ast, BV, Bool, Dynamic}};

use symbolic_vm::{
  plugin::{IntegerArithmeticPlugin, PluginManager, Specification, VerificationPlugin},
  runtime::vm::SymbolicVM,
  state::vm_context::SymbolicVMContext,
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

pub struct AbsSpec<'a, 'ctx> {
  right: Specification<'a, 'ctx>,
  wrong: Specification<'a, 'ctx>,
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
      .add_write_set(GENESIS_CHANGE_SET.clone().write_set());
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
    let mut vm_ctx = SymbolicVMContext::new(&context, GasUnits::new(0), &data_cache);
    let mut metadata = TransactionMetadata::default();
    metadata.sender = AccountAddress::random();

    let z3_ctx = &context;
    let int_plugin = IntegerArithmeticPlugin::new();
    let target_spec = Specification::new(
      |_a: &[SymValue]| SymBool::from(z3_ctx, true),
      |_a: &[SymValue], r: &[SymValue]| {
        VMSymValueCast::<SymBool>::cast(r[0].copy_value()).unwrap()
      },
      |_a: &[SymValue]| SymBool::from(z3_ctx, true)
    );
    let abs_spec_wrong = Specification::new(
      |_a: &[SymValue]| SymBool::from(z3_ctx, true),
      |_a: &[SymValue], r: &[SymValue]| {
        // TODO: bad type conversions and clones
        // TODO: figure it out
        let ret = VMSymValueCast::<SymU64>::cast(r[0].copy_value()).unwrap();
        SymBool::from_ast(
          ret.as_inner().bvuge(&BV::from_u64(z3_ctx, 10, 64)),
          vec![Dynamic::from_ast(ret.as_inner())],
        )
      },
      |_a: &[SymValue]| SymBool::from(z3_ctx, true)
    );
    let abs_spec_right = Specification::new(
      |_a: &[SymValue]| SymBool::from(z3_ctx, true),
      |a: &[SymValue], r: &[SymValue]| {
        // TODO: bad type conversions and clones
        // TODO: figure it out
        let arg = VMSymValueCast::<SymU64>::cast(a[0].copy_value()).unwrap();
        let ret = VMSymValueCast::<SymU64>::cast(r[0].copy_value()).unwrap();
        let const_ten = BV::from_u64(z3_ctx, 10, 64);
        let arg_ast = arg.as_inner();
        let ret_ast = ret.as_inner();
        let cond_pos = arg_ast.bvuge(&const_ten).implies(&ret_ast._eq(&arg_ast));
        let cond_neg = arg_ast.bvult(&const_ten).implies(&ret_ast._eq(&const_ten.bvsub(&arg_ast)));
        let cond = Bool::and(z3_ctx, &[&cond_pos, &cond_neg]);
        SymBool::from_ast(cond, vec![Dynamic::from_ast(arg_ast), Dynamic::from_ast(ret_ast)]) // TODO: Should not be vec![]
      },
      |_a: &[SymValue]| SymBool::from(z3_ctx, true)
    );
    let abs_spec = AbsSpec {
      wrong: abs_spec_wrong,
      right: abs_spec_right,
    };
    let mut verification_plugin = VerificationPlugin::new(&context, target_spec);
    let func_name = Identifier::new("abs_on_ten").unwrap();
    verification_plugin.add_spec(func_name, abs_spec.wrong);
    let mut plugin_manager = PluginManager::new();
    plugin_manager.add_plugin(int_plugin);
    plugin_manager.add_plugin(verification_plugin);
  
    vm.execute_function(module, function_name, &mut vm_ctx, &metadata, &mut plugin_manager)
      .expect("VM should run correctly");
  }
}
