use diem_types::{
  access_path::AccessPath,
  // vm_error::{StatusCode, VMStatus},
  // write_set::WriteSet,
};
use move_core_types::{
  gas_schedule::{GasCarrier, GasUnits},
  language_storage::ModuleId,
  value::MoveStructLayout,
};
use move_vm_runtime::data_cache::RemoteCache;
use crate::{
  types::{values::SymGlobalValue},
  state::{
    data_cache::SymbolicExecutionDataCache,
    interpreter_state::SymInterpreterState,
  },
};
use vm::errors::VMResult;

use z3::Context;

pub struct SymbolicVMContext<'vtxn, 'ctx> {
  /// Gas metering to track cost of execution.
  gas_left: GasUnits<GasCarrier>,
  /// Data store
  data_view: SymbolicExecutionDataCache<'vtxn, 'ctx>,
}

/// Context for SymInterpreter
/// Provides interface of gas, resources, modules
/// The context is read-only for gas and resources, SymInterpreter should
/// only change its intermediate state
impl<'vtxn, 'ctx> SymbolicVMContext<'vtxn, 'ctx> {
  pub fn new(
    z3_ctx: &'ctx Context,
    gas_left: GasUnits<GasCarrier>,
    data_cache: &'vtxn dyn RemoteCache
  ) -> Self {
    Self {
      gas_left,
      data_view: SymbolicExecutionDataCache::new(z3_ctx, data_cache),
    }
  }

  pub fn create_intermediate_state(&self) -> SymInterpreterState<'ctx>{
    SymInterpreterState::new(self.data_view.get_context(), self.gas_left)
  }

  // Gas
  pub fn remaining_gas(&self) -> GasUnits<GasCarrier> {
    self.gas_left
  }

  // Resource
  pub(crate) fn load_data(
    &mut self,
    ap: &AccessPath,
    ty: &MoveStructLayout,
  ) -> PartialVMResult<&Option<(MoveStructLayout, SymGlobalValue<'ctx>)>> {
    self.data_view.load_data(ap, ty).map(|x| &*x)
  }

  // Modules
  pub fn load_module(&self, module: &ModuleId) -> PartialVMResult<Vec<u8>> {
    self.data_view.load_module(module)
  }

  pub fn publish_module(&mut self, module_id: ModuleId, module: Vec<u8>) -> PartialVMResult<()> {
    self.data_view.publish_module(module_id, module)
  }

  pub fn exists_module(&self, key: &ModuleId) -> bool {
    self.data_view.exists_module(key)
  }
}
