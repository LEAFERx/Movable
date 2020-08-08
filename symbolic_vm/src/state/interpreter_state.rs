use libra_types::{
  access_path::AccessPath,
  contract_event::ContractEvent,
  vm_error::{sub_status, StatusCode, VMStatus},
  // write_set::WriteSet,
};
use libra_logger::prelude::*;
use move_core_types::{
  gas_schedule::{AbstractMemorySize, GasAlgebra, GasCarrier, GasUnits},
};
use move_vm_types::loaded_data::types::FatStructType;
use crate::{
  types::{
    values::{SymGlobalValue, SymStruct, SymValue},
  },
  state::{
    vm_context::SymbolicVMContext,
  },
};
use vm::errors::*;

use std::{
  collections::BTreeMap,
};

use z3::Context;

pub struct SymInterpreterState<'ctx> {
  context: &'ctx Context,

  /// Gas metering to track cost of execution.
  gas_left: GasUnits<GasCarrier>,
  /// List of events "fired" during the course of an execution.
  event_data: Vec<ContractEvent>,

  data_map: BTreeMap<AccessPath, Option<(FatStructType, SymGlobalValue<'ctx>)>>,

  // phantom: PhantomData<SymbolicVMContext<'_, 'ctx>>,
}

impl<'ctx> SymInterpreterState<'ctx> {
  pub(in crate::state) fn new(
    context: &'ctx Context,
    gas_left: GasUnits<GasCarrier>,
  ) -> Self {
    Self {
      context,
      gas_left,
      event_data: Vec::new(),
      data_map: BTreeMap::new(),
    }
  }

  // Gas
  pub fn deduct_gas(&mut self, amount: GasUnits<GasCarrier>) -> VMResult<()> {
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
  
  pub fn remaining_gas(&self) -> GasUnits<GasCarrier> {
    self.gas_left
  }

  // Resources
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
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<&mut Option<(FatStructType, SymGlobalValue<'ctx>)>> {
    if !self.data_map.contains_key(ap) {
      let context_data = vm_ctx
        .load_data(ap, ty)?
        .as_ref()
        .map(|(ty, g)| (ty.clone(), g.clone_for_symbolic_state_fork()));
      match context_data {
        Some(map_entry) => {
          self.data_map.insert(ap.clone(), Some(map_entry));
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

  pub fn borrow_resource(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<Option<&SymGlobalValue<'ctx>>> {
    let map_entry = self.load_data(vm_ctx, ap, ty)?;
    Ok(map_entry.as_ref().map(|(_, g)| g))
  }

  pub fn move_resource(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<Option<SymGlobalValue<'ctx>>> {
    let map_entry = self.load_data(vm_ctx, ap, ty)?;
    // .take() means that the entry is removed from the data map -- this marks the
    // access path for deletion.
    Ok(map_entry.take().map(|(_, g)| g))
  }

  pub fn move_resource_to(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType,
    resource: SymStruct<'ctx>,
  ) -> VMResult<()> {
    // a resource can be written to an AccessPath if the data does not exists or
    // it was deleted (MoveFrom)
    let can_write = match self.borrow_resource(vm_ctx, ap, ty) {
      Ok(None) => true,
      Ok(Some(_)) => false,
      Err(e) => match e.major_status {
        StatusCode::MISSING_DATA => true,
        _ => return Err(e),
      },
    };
    if can_write {
      let new_root = SymGlobalValue::new(SymValue::from_sym_struct(resource))?;
      new_root.mark_dirty()?;
      self.publish_resource(ap, (ty.clone(), new_root))
    } else {
      warn!("[VM] Cannot write over existing resource {}", ap);
      Err(vm_error(
        Location::new(),
        StatusCode::CANNOT_WRITE_EXISTING_RESOURCE,
      ))
    }
  }

  pub fn move_resource_from(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType
  ) -> VMResult<SymValue<'ctx>> {
    let resource = self
      .load_data(vm_ctx, ap, ty)
      .map(|e| e.take().map(|(_, g)| g));
    let root_value = match self.move_resource(vm_ctx, ap, ty) {
      Ok(g) => g,
      Err(e) => {
        warn!("[VM] (MoveFrom) Error reading data for {}: {:?}", ap, e);
        return Err(e);
      }
    };

    match root_value {
      Some(global_val) => Ok(SymValue::from_sym_struct(global_val.into_owned_struct()?)),
      None => Err(
        vm_error(Location::new(), StatusCode::DYNAMIC_REFERENCE_ERROR)
          .with_sub_status(sub_status::DRE_GLOBAL_ALREADY_BORROWED),
      ),
    }
  }

  pub fn resource_exists(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType,
  ) -> VMResult<(bool, AbstractMemorySize<GasCarrier>)> {
    Ok(match self.borrow_resource(vm_ctx, ap, ty) {
      Ok(Some(gref)) => (true, gref.size()),
      Ok(None) | Err(_) => (false, AbstractMemorySize::new(0)),
    })
  }

  pub fn borrow_global(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
    ap: &AccessPath,
    ty: &FatStructType
  ) -> VMResult<&SymGlobalValue<'ctx>> {
    match self.borrow_resource(vm_ctx, ap, ty) {
      Ok(Some(g)) => Ok(g),
      Ok(None) => Err(
        // TODO: wrong status code?
        vm_error(Location::new(), StatusCode::DYNAMIC_REFERENCE_ERROR)
          .with_sub_status(sub_status::DRE_GLOBAL_ALREADY_BORROWED),
      ),
      Err(e) => {
        error!("[VM] (BorrowGlobal) Error reading data for {}: {:?}", ap, e);
        Err(e)
      }
    }
  }

  // Events
  pub fn push_event(&mut self, event: ContractEvent) {
    self.event_data.push(event)
  }
}

impl<'ctx> Clone for SymInterpreterState<'ctx> {
  fn clone(&self) -> Self {
    Self {
      context: self.context,
      gas_left: self.gas_left,
      event_data: self.event_data.clone(),
      data_map: self.data_map.iter().map(|(key, value)| {
        let cloned_key = key.clone();
        let cloned_value = match value {
          Some((ty, val)) => Some((ty.clone(), val.clone_for_symbolic_state_fork())),
          None => None
        };
        (cloned_key, cloned_value)
      }).collect(),
    }
  }
}
