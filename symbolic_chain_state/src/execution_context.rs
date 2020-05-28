use crate::data_cache::SymbolicExecutionDataCache;
use libra_types::{
  access_path::AccessPath,
  contract_event::ContractEvent,
  vm_error::{StatusCode, VMStatus},
  write_set::WriteSet,
};
use move_core_types::{
  gas_schedule::{GasAlgebra, GasCarrier, GasUnits},
  language_storage::ModuleId,
};
use move_vm_state::data_cache::RemoteCache;
use move_vm_types::loaded_data::types::FatStructType;
use symbolic_vm::types::{chain_state::SymChainState, values::SymGlobalValue};
use vm::errors::VMResult;

use solver::Solver;

pub struct SymbolicExecutionContext<'vtxn, 'ctx> {
  /// Gas metering to track cost of execution.
  gas_left: GasUnits<GasCarrier>,
  /// List of events "fired" during the course of an execution.
  event_data: Vec<ContractEvent>,
  /// Data store
  data_view: SymbolicExecutionDataCache<'vtxn, 'ctx>,
}

impl<'vtxn, 'ctx> SymbolicExecutionContext<'vtxn, 'ctx> {
  pub fn new(
    solver: &'ctx Solver<'ctx>,
    gas_left: GasUnits<GasCarrier>,
    data_cache: &'vtxn dyn RemoteCache
  ) -> Self {
    Self {
      gas_left,
      event_data: Vec::new(),
      data_view: SymbolicExecutionDataCache::new(solver, data_cache),
    }
  }
}

impl<'vtxn, 'ctx> SymChainState<'ctx> for SymbolicExecutionContext<'vtxn, 'ctx> {
  fn deduct_gas(&mut self, amount: GasUnits<GasCarrier>) -> VMResult<()> {
    if self
      .gas_left
      .app(&amount, |curr_gas, gas_amt| curr_gas >= gas_amt)
    {
      self.gas_left = self.gas_left.sub(amount);
      Ok(())
    } else {
      // Zero out the internal gas state
      self.gas_left = GasUnits::new(0);
      Err(VMStatus::new(StatusCode::OUT_OF_GAS))
    }
  }

  fn remaining_gas(&self) -> GasUnits<GasCarrier> {
    self.gas_left
  }

  fn borrow_resource(
    &mut self,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<Option<&SymGlobalValue<'ctx>>> {
    let map_entry = self.data_view.load_data(ap, ty)?;
    Ok(map_entry.as_ref().map(|(_, g)| g))
  }

  fn move_resource_from(
    &mut self,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<Option<SymGlobalValue<'ctx>>> {
    let map_entry = self.data_view.load_data(ap, ty)?;
    // .take() means that the entry is removed from the data map -- this marks the
    // access path for deletion.
    Ok(map_entry.take().map(|(_, g)| g))
  }

  fn load_module(&self, module: &ModuleId) -> VMResult<Vec<u8>> {
    self.data_view.load_module(module)
  }

  fn publish_module(&mut self, module_id: ModuleId, module: Vec<u8>) -> VMResult<()> {
    self.data_view.publish_module(module_id, module)
  }

  fn publish_resource(
    &mut self,
    ap: &AccessPath,
    g: (FatStructType, SymGlobalValue<'ctx>),
  ) -> VMResult<()> {
    self.data_view.publish_resource(ap, g)
  }

  fn exists_module(&self, key: &ModuleId) -> bool {
    self.data_view.exists_module(key)
  }

  fn emit_event(&mut self, event: ContractEvent) {
    self.event_data.push(event)
  }
}
