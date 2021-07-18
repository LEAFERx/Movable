// use diem_logger::prelude::*;
// use diem_state_view::StateView;
use crate::{
  runtime::{
    context::TypeContext,
    loader::Loader,
  },
  types::{
    data_store::SymDataStore,
    effects::{SymAccountChangeSet, SymChangeSet, SymEvent},
    memory::SymMemory,
    values::{SymAccountAddress, SymGlobalValue, SymGlobalValueEffect, SymValue},
  },
};
use move_core_types::{
  account_address::AccountAddress,
  identifier::Identifier,
  language_storage::{ModuleId, TypeTag, StructTag},
  value::MoveTypeLayout,
  vm_status::StatusCode,
};
use move_vm_runtime::data_cache::RemoteCache;
use move_vm_types::{loaded_data::runtime_types::Type, values::Value};
use std::collections::btree_map::BTreeMap;
use vm::errors::*;

use z3::Context;

pub struct SymAccountDataCache {
  // data_map: BTreeMap<Type, (MoveTypeLayout, SymGlobalValue<'ctx>)>,
  module_map: BTreeMap<Identifier, Vec<u8>>,
}

impl SymAccountDataCache {
  fn new() -> Self {
    Self {
      // data_map: BTreeMap::new(),
      module_map: BTreeMap::new(),
    }
  }

  fn fork(&self) -> Self {
    Self {
      // data_map: self.data_map
      //   .iter().map(|(key, value)| {
      //     let cloned_key = key.clone();
      //     let cloned_value = (value.0.clone(), value.1.fork());
      //     (cloned_key, cloned_value)
      //   })
      //   .collect(),
      module_map: self.module_map.clone(),
    }
  }
}

pub struct SymDataCache<'ctx, 'r, 'l, R> {
  z3_ctx: &'ctx Context,
  ty_ctx: &'l TypeContext<'ctx>,
  remote: &'r R,
  loader: &'l Loader,
  memory: SymMemory<'ctx>,
  account_map: BTreeMap<AccountAddress, SymAccountDataCache>,
  event_data: Vec<(Vec<u8>, u64, Type, MoveTypeLayout, SymValue<'ctx>)>,
}

impl<'ctx, 'r, 'l, R: RemoteCache> SymDataCache<'ctx, 'r, 'l, R> {
  pub(crate) fn new(z3_ctx: &'ctx Context, ty_ctx: &'l TypeContext<'ctx>, remote: &'r R, loader: &'l Loader) -> Self {
    Self {
      z3_ctx,
      ty_ctx,
      remote,
      loader,
      account_map: BTreeMap::new(),
      memory: SymMemory::new(z3_ctx, ty_ctx),
      event_data: vec![],
    }
  }

  pub fn fork(&self) -> Self {
    Self {
      z3_ctx: self.z3_ctx,
      ty_ctx: self.ty_ctx,
      remote: self.remote,
      loader: self.loader,
      account_map: self.account_map.iter().map(|(addr, data)| (addr.clone(), data.fork())).collect(),
      memory: self.memory.fork(),
      event_data: self.event_data.iter().map(|(guid, seq, ty, layout, val)| {
        (guid.clone(), *seq, ty.clone(), layout.clone(), val.copy_value().unwrap())
      }).collect(),
    }
  }

  // pub fn into_effects(self) -> PartialVMResult<(SymChangeSet<'ctx>, Vec<SymEvent<'ctx>>)> {
  //   let mut account_changesets = BTreeMap::new();
  //   for (addr, account_data_cache) in self.account_map.into_iter() {
  //     let mut modules = BTreeMap::new();
  //     for (module_name, module_blob) in account_data_cache.module_map {
  //       modules.insert(module_name, Some(module_blob));
  //     }

  //     let mut resources = BTreeMap::new();
  //     for (ty, (layout, gv)) in account_data_cache.data_map {
  //       match gv.into_effect()? {
  //         SymGlobalValueEffect::None => (),
  //         SymGlobalValueEffect::Deleted => {
  //           let struct_tag = match self.loader.type_to_type_tag(&ty)? {
  //             TypeTag::Struct(struct_tag) => struct_tag,
  //             _ => return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)),
  //           };
  //           resources.insert(struct_tag, None);
  //         }
  //         SymGlobalValueEffect::Changed(val) => {
  //           let struct_tag = match self.loader.type_to_type_tag(&ty)? {
  //             TypeTag::Struct(struct_tag) => struct_tag,
  //             _ => return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR)),
  //           };
  //           resources.insert(struct_tag, Some(val));
  //         }
  //       }
  //     }

  //     account_changesets.insert(addr, SymAccountChangeSet { modules, resources });
  //   }

  //   let mut events = vec![];
  //   for (guid, seq_num, ty, ty_layout, val) in self.event_data {
  //     let ty_tag = self.loader.type_to_type_tag(&ty)?;
  //     events.push((guid, seq_num, ty_tag, val))
  //   }

  //   Ok((
  //     SymChangeSet {
  //       accounts: account_changesets,
  //     },
  //     events,
  //   ))
  // }

  // pub fn num_mutated_accounts(&self, sender: &AccountAddress) -> u64 {
  //   // The sender's account will always be mutated.
  //   let mut total_mutated_accounts: u64 = 1;
  //   for (addr, entry) in self.account_map.iter() {
  //     if addr != sender && entry.data_map.values().any(|(_, v)| v.is_mutated()) {
  //       total_mutated_accounts += 1;
  //     }
  //   }
  //   total_mutated_accounts
  // }

  fn get_mut_or_insert_with<'a, K, V, F>(map: &'a mut BTreeMap<K, V>, k: &K, gen: F) -> &'a mut V
  where
    F: FnOnce() -> (K, V),
    K: Ord,
  {
    if !map.contains_key(k) {
      let (k, v) = gen();
      map.insert(k, v);
    }
    map.get_mut(k).unwrap()
  }
}

impl<'ctx, 'r, 'l, R: RemoteCache> SymDataStore<'ctx> for SymDataCache<'ctx, 'r, 'l, R> {
  fn get_z3_ctx(&self) -> &'ctx Context {
    self.z3_ctx
  }

  fn get_ty_ctx(&self) -> &TypeContext<'ctx> {
    self.ty_ctx
  }

  // Retrieve data from the local cache or loads it from the remote cache into the local cache.
  // All operations on the global data are based on this API and they all load the data
  // into the cache.
  // fn load_resource(
  //   &mut self,
  //   addr: AccountAddress,
  //   ty: &Type,
  // ) -> PartialVMResult<&mut SymGlobalValue<'ctx>> {
  //   let account_cache = Self::get_mut_or_insert_with(&mut self.account_map, &addr, || {
  //     (addr, SymAccountDataCache::new())
  //   });

  //   if !account_cache.data_map.contains_key(ty) {
  //     let ty_tag = match self.loader.type_to_type_tag(ty)? {
  //       TypeTag::Struct(s_tag) => s_tag,
  //       _ =>
  //       // non-struct top-level value; can't happen
  //       {
  //         return Err(PartialVMError::new(StatusCode::INTERNAL_TYPE_ERROR))
  //       }
  //     };
  //     let ty_layout = self.loader.type_to_type_layout(ty)?;

  //     let gv = match self.remote.get_resource(&addr, &ty_tag) {
  //       Ok(Some(blob)) => {
  //         let val = match Value::simple_deserialize(&blob, &ty_layout) {
  //           Some(val) => {
  //             let ty_tag = TypeTag::Struct(ty_tag);
  //             SymValue::from_deserialized_value(self.z3_ctx, self.ty_ctx, val, ty_tag)?
  //           },
  //           None => {
  //             let msg = format!("Failed to deserialize resource {} at {}!", ty_tag, addr);
  //             return Err(
  //               PartialVMError::new(StatusCode::FAILED_TO_DESERIALIZE_RESOURCE).with_message(msg),
  //             );
  //           }
  //         };

  //         SymGlobalValue::cached(val)?
  //       }
  //       Ok(None) => SymGlobalValue::none(),
  //       Err(err) => {
  //         let msg = format!("Unexpected storage error: {:?}", err);
  //         // REVIEW: better way to get info out of a PartialVMError?
  //         let (_old_status, _old_sub_status, _old_message, indices, offsets) = err.all_data();
  //         return Err(
  //           PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
  //             .with_message(msg)
  //             .at_indices(indices)
  //             .at_code_offsets(offsets),
  //         );
  //       }
  //     };

  //     account_cache.data_map.insert(ty.clone(), (ty_layout, gv));
  //   }

  //   Ok(
  //     account_cache
  //       .data_map
  //       .get_mut(ty)
  //       .map(|(_ty_layout, gv)| gv)
  //       .expect("global value must exist"),
  //   )
  // }

  fn load_resource(
    &mut self,
    addr: SymAccountAddress<'ctx>,
    ty: &Type,
  ) -> PartialVMResult<SymGlobalValue<'ctx>> {
    let ty = self.loader.type_to_type_tag(ty)?;
    self.memory.load_resource(self.z3_ctx, self.ty_ctx, addr, ty)
  }

  fn write_resource(
    &mut self,
    val: &SymGlobalValue<'ctx>
  ) -> PartialVMResult<()> {
    self.memory.write_resource(self.z3_ctx, self.ty_ctx, val)
  }

  fn load_module(&self, module_id: &ModuleId) -> VMResult<Vec<u8>> {
    if let Some(account_cache) = self.account_map.get(module_id.address()) {
      if let Some(blob) = account_cache.module_map.get(module_id.name()) {
        return Ok(blob.clone());
      }
    }
    match self.remote.get_module(module_id) {
      Ok(Some(bytes)) => Ok(bytes),
      Ok(None) => Err(
        PartialVMError::new(StatusCode::LINKER_ERROR)
          .with_message(format!("Cannot find {:?} in data cache", module_id))
          .finish(Location::Undefined),
      ),
      Err(err) => {
        let msg = format!("Unexpected storage error: {:?}", err);
        let (_old_status, _old_sub_status, _old_message, location, indices, offsets) =
          err.all_data();
        Err(
          PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message(msg)
            .at_indices(indices)
            .at_code_offsets(offsets)
            .finish(location),
        )
      }
    }
  }

  fn publish_module(&mut self, module_id: &ModuleId, blob: Vec<u8>) -> VMResult<()> {
    let account_cache =
      Self::get_mut_or_insert_with(&mut self.account_map, module_id.address(), || {
        (*module_id.address(), SymAccountDataCache::new())
      });

    account_cache
      .module_map
      .insert(module_id.name().to_owned(), blob);

    Ok(())
  }

  fn exists_module(&self, module_id: &ModuleId) -> VMResult<bool> {
    if let Some(account_cache) = self.account_map.get(module_id.address()) {
      if account_cache.module_map.contains_key(module_id.name()) {
        return Ok(true);
      }
    }
    Ok(self.remote.get_module(module_id)?.is_some())
  }

  fn emit_event(
    &mut self,
    guid: Vec<u8>,
    seq_num: u64,
    ty: Type,
    val: SymValue<'ctx>,
  ) -> PartialVMResult<()> {
    let ty_layout = self.loader.type_to_type_layout(&ty)?;
    Ok(self.event_data.push((guid, seq_num, ty, ty_layout, val)))
  }
}
