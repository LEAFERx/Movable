// use diem_logger::prelude::*;
// use diem_state_view::StateView;
use diem_types::{
  access_path::AccessPath,
  // on_chain_config::ConfigStorage,
  // write_set::{WriteOp, WriteSet, WriteSetMut},
};
use move_core_types::{
  language_storage::ModuleId,
  value::MoveStructLayout,
  vm_status::{StatusCode, VMStatus},
};
use move_vm_types::{
  values::{Struct},
};
use crate::types::values::{SymGlobalValue, /* SymStruct, */ SymValue};
use move_vm_runtime::data_cache::RemoteCache;
use std::{collections::btree_map::BTreeMap, /* mem::replace */};
use vm::errors::*;

use z3::Context;

pub struct SymbolicExecutionDataCache<'vtxn, 'ctx> {
  z3_ctx: &'ctx Context,
  data_map: BTreeMap<AccessPath, Option<(MoveStructLayout, SymGlobalValue<'ctx>)>>,
  module_map: BTreeMap<ModuleId, Vec<u8>>,
  data_cache: &'vtxn dyn RemoteCache,
}

impl<'vtxn, 'ctx> SymbolicExecutionDataCache<'vtxn, 'ctx> {
  pub fn new(z3_ctx: &'ctx Context, data_cache: &'vtxn dyn RemoteCache) -> Self {
    SymbolicExecutionDataCache {
      z3_ctx,
      data_cache,
      data_map: BTreeMap::new(),
      module_map: BTreeMap::new(),
    }
  }

  pub fn get_context(&self) -> &'ctx Context {
    self.z3_ctx
  }

  pub fn exists_module(&self, m: &ModuleId) -> bool {
    self.module_map.contains_key(m) || {
      let ap = AccessPath::from(m);
      matches!(self.data_cache.get(&ap), Ok(Some(_)))
    }
  }

  pub fn load_module(&self, module: &ModuleId) -> PartialVMResult<Vec<u8>> {
    match self.module_map.get(module) {
      Some(bytes) => Ok(bytes.clone()),
      None => {
        let ap = AccessPath::from(module);
        self.data_cache.get(&ap).and_then(|data| {
          data.ok_or_else(|| {
            PartialVMError::new(StatusCode::LINKER_ERROR)
              .with_message(format!("Cannot find {:?} in data cache", module))
          })
        })
      }
    }
  }

  pub fn publish_module(&mut self, m: ModuleId, bytes: Vec<u8>) -> PartialVMResult<()> {
    self.module_map.insert(m, bytes);
    Ok(())
  }

  pub fn publish_resource(
    &mut self,
    ap: &AccessPath,
    g: (MoveStructLayout, SymGlobalValue<'ctx>),
  ) -> PartialVMResult<()> {
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
    ty: &MoveStructLayout,
  ) -> PartialVMResult<&mut Option<(MoveStructLayout, SymGlobalValue<'ctx>)>> {
    if !self.data_map.contains_key(ap) {
      match self.data_cache.get(ap)? {
        Some(bytes) => {
          let res = Struct::simple_deserialize(&bytes, ty)?;
          let gr = SymGlobalValue::new(SymValue::from_deserialized_struct(self.context, res, ty)?)?;
          self.data_map.insert(ap.clone(), Some((ty.clone(), gr)));
        }
        None => {
          return Err(
            PartialVMError::new(StatusCode::MISSING_DATA).with_message(format!(
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
  // pub fn make_write_set(&mut self) -> PartialVMResult<WriteSet> {
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

  pub fn get_remote_cache(&self) -> &'vtxn dyn RemoteCache {
    self.data_cache
  }
}

impl<'vtxn, 'ctx> Clone for SymbolicExecutionDataCache<'vtxn, 'ctx> {
  fn clone(&self) -> Self {
    Self {
      z3_ctx: self.z3_ctx,
      data_map: self.data_map.iter().map(|(key, value)| {
        let cloned_key = key.clone();
        let cloned_value = match value {
          Some((ty, val)) => Some((ty.clone(), val.clone_for_symbolic_state_fork())),
          None => None
        };
        (cloned_key, cloned_value)
      }).collect(),
      module_map: self.module_map.clone(),
      data_cache: self.data_cache,
    }
  }
}