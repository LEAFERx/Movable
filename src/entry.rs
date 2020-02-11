use vm::{
  errors::*,
};

use vm_runtime::{
  chain_state::TransactionExecutionContext,
};

use symbolic_vm::{
  runtime::SymVMRuntime,
};

fn main() {
  TransactionExecutionContext::new(gas_left: GasUnits<GasCarrier>, data_cache: &'txn dyn RemoteCache)
}