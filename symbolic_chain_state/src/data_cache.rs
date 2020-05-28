use libra_logger::prelude::*;
use libra_state_view::StateView;
use libra_types::{
  access_path::AccessPath,
  on_chain_config::ConfigStorage,
  vm_error::{StatusCode, VMStatus},
  write_set::{WriteOp, WriteSet, WriteSetMut},
};
use move_core_types::language_storage::ModuleId;
use move_vm_types::{
  loaded_data::types::FatStructType,
  values::{Struct},
};
use symbolic_vm::types::values::{SymGlobalValue, SymStruct, SymValue};
use move_vm_state::data_cache::RemoteCache;
use std::{collections::btree_map::BTreeMap, mem::replace};
use vm::errors::*;

use solver::Solver;

pub struct SymbolicExecutionDataCache<'vtxn, 'ctx> {
  solver: &'ctx Solver<'ctx>,
  data_map: BTreeMap<AccessPath, Option<(FatStructType, SymGlobalValue<'ctx>)>>,
  module_map: BTreeMap<ModuleId, Vec<u8>>,
  data_cache: &'vtxn dyn RemoteCache,
}

impl<'txn, 'ctx> SymbolicExecutionDataCache<'txn, 'ctx> {
  pub fn new(solver: &'ctx Solver<'ctx>, data_cache: &'txn dyn RemoteCache) -> Self {
    SymbolicExecutionDataCache {
      solver,
      data_cache,
      data_map: BTreeMap::new(),
      module_map: BTreeMap::new(),
    }
  }

  pub fn exists_module(&self, m: &ModuleId) -> bool {
    self.module_map.contains_key(m) || {
      let ap = AccessPath::from(m);
      matches!(self.data_cache.get(&ap), Ok(Some(_)))
    }
  }

  pub fn load_module(&self, module: &ModuleId) -> VMResult<Vec<u8>> {
    match self.module_map.get(module) {
      Some(bytes) => Ok(bytes.clone()),
      None => {
        let ap = AccessPath::from(module);
        self.data_cache.get(&ap).and_then(|data| {
          data.ok_or_else(|| {
            VMStatus::new(StatusCode::LINKER_ERROR)
              .with_message(format!("Cannot find {:?} in data cache", module))
          })
        })
      }
    }
  }

  pub fn publish_module(&mut self, m: ModuleId, bytes: Vec<u8>) -> VMResult<()> {
    self.module_map.insert(m, bytes);
    Ok(())
  }

  pub fn publish_resource(
    &mut self,
    ap: &AccessPath,
    g: (FatStructType, SymGlobalValue<'ctx>),
  ) -> VMResult<()> {
    self.data_map.insert(ap.clone(), Some(g));
    Ok(())
  }

  // Retrieve data from the local cache or loads it from the remote cache into the local cache.
  // All operations on the global data are based on this API and they all load the data
  // into the cache.
  // TODO: this may not be the most efficient model because we always load data into the
  // cache even when that would not be strictly needed. Review once we have the whole story
  // working
  pub(crate) fn load_data(
    &mut self,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<&mut Option<(FatStructType, SymGlobalValue<'ctx>)>> {
    if !self.data_map.contains_key(ap) {
      match self.data_cache.get(ap)? {
        Some(bytes) => {
          let res = Struct::simple_deserialize(&bytes, ty)?;
          let gr = SymGlobalValue::new(SymValue::from_deserialized_struct(self.solver, res, ty)?)?;
          self.data_map.insert(ap.clone(), Some((ty.clone(), gr)));
        }
        None => {
          return Err(
            VMStatus::new(StatusCode::MISSING_DATA).with_message(format!(
              "Cannot find {:?}::{}::{} for Access Path: {:?}",
              &ty.address,
              &ty.module.as_str(),
              &ty.name.as_str(),
              ap
            )),
          );
        }
      };
    }
    Ok(self.data_map.get_mut(ap).expect("data must exist"))
  }

  /// Make a write set from the updated (dirty, deleted) global resources along with
  /// to-be-published modules.
  /// Consume the TransactionDataCache and must be called at the end of a transaction.
  /// This also ends up checking that reference count around global resources is correct
  /// at the end of the transactions (all ReleaseRef are properly called)
  // pub fn make_write_set(&mut self) -> VMResult<WriteSet> {
  //   if self.data_map.len() + self.module_map.len() > usize::max_value() {
  //     return Err(vm_error(Location::new(), StatusCode::INVALID_DATA));
  //   }

  //   let mut sorted_ws: BTreeMap<AccessPath, WriteOp> = BTreeMap::new();

  //   let data_map = replace(&mut self.data_map, BTreeMap::new());
  //   for (key, global_val) in data_map {
  //     match global_val {
  //       Some((layout, global_val)) => {
  //         if !global_val.is_clean()? {
  //           // into_owned_struct will check if all references are properly released
  //           // at the end of a transaction
  //           let data = global_val.into_owned_struct()?;
  //           let blob = match data.simple_serialize(&layout) {
  //             Some(blob) => blob,
  //             None => {
  //               return Err(vm_error(
  //                 Location::new(),
  //                 StatusCode::VALUE_SERIALIZATION_ERROR,
  //               ))
  //             }
  //           };
  //           sorted_ws.insert(key, WriteOp::Value(blob));
  //         }
  //       }
  //       None => {
  //         sorted_ws.insert(key, WriteOp::Deletion);
  //       }
  //     }
  //   }

  //   let module_map = replace(&mut self.module_map, BTreeMap::new());
  //   for (module_id, module) in module_map {
  //     sorted_ws.insert((&module_id).into(), WriteOp::Value(module));
  //   }

  //   let mut write_set = WriteSetMut::new(Vec::new());
  //   for (key, value) in sorted_ws {
  //     write_set.push((key, value));
  //   }
  //   write_set
  //     .freeze()
  //     .map_err(|_| vm_error(Location::new(), StatusCode::DATA_FORMAT_ERROR))
  // }

  /// Flush out the cache and restart from a clean state
  pub fn clear(&mut self) {
    self.data_map.clear();
    self.module_map.clear();
  }
}
