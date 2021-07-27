// use diem_logger::prelude::*;
use move_core_types::{
  account_address::AccountAddress,
  // gas_schedule::CostTable,
  identifier::IdentStr,
  language_storage::{ModuleId, TypeTag},
  vm_status::StatusCode,
};
use move_vm_types::loaded_data::runtime_types::Type;
use move_vm_runtime::{
  data_cache::RemoteCache,
  logging::NoContextLog,
};
use crate::{
  runtime::{
    data_cache::SymDataCache,
    interpreter::{
      SymInterpreter, SymInterpreterForkResult, SymInterpreterExecutionResult, ExecutionReport,
    },
    loader::Loader,
  },
  types::data_store::SymDataStore,
};
use vm::{
  access::ModuleAccess,
  compatibility::Compatibility,
  errors::{verification_error, Location, VMResult, PartialVMResult, PartialVMError},
  file_format::CompiledModule,
  IndexKind,
  normalized,
};

use std::{
  marker::PhantomData,
  sync::Arc,
};

use z3::Context;

use crate::{
  plugin::PluginManager,
  types::values::{SymValue, SymbolicMoveValue},
  runtime::{
    context::TypeContext,
    loader::Function,
    session::Session,
  },
};

/// An instantiation of the MoveVM.
pub(crate) struct VMRuntime<'ctx> {
  loader: Loader,
  type_context: TypeContext<'ctx>,
}

impl<'ctx> VMRuntime<'ctx> {
  pub fn new(z3_ctx: &'ctx Context) -> Self {
    VMRuntime {
      loader: Loader::new(),
      type_context: TypeContext::new(z3_ctx)
    }
  }

  pub fn new_session<'r, R: RemoteCache>(&self, z3_ctx: &'ctx Context, remote: &'r R) -> Session<'ctx, 'r, '_, R> {
    Session {
      z3_ctx,
      runtime: self,
      data_cache: SymDataCache::new(z3_ctx, &self.type_context, remote, &self.loader),
    }
  }

  pub(crate) fn ty_ctx(&self) -> &TypeContext<'ctx> {
    &self.type_context
  }

  pub(crate) fn publish_module(
    &self,
    module: Vec<u8>,
    sender: AccountAddress,
    data_cache: &mut SymDataCache<'ctx, '_, '_, impl RemoteCache>,
  ) -> VMResult<()> {
    let log_context = NoContextLog::new();

    let compiled_module = match CompiledModule::deserialize(&module) {
      Ok(module) => module,
      Err(err) => {
        // warn!("[VM] module deserialization failed {:?}", err);
        return Err(err.finish(Location::Undefined));
      }
    };

    // Make sure the module's self address matches the transaction sender. The self address is
    // where the module will actually be published. If we did not check this, the sender could
    // publish a module under anyone's account.
    if compiled_module.address() != &sender {
      return Err(verification_error(
        StatusCode::MODULE_ADDRESS_DOES_NOT_MATCH_SENDER,
        IndexKind::AddressIdentifier,
        compiled_module.self_handle_idx().0,
      )
      .finish(Location::Undefined));
    }

    // Make sure that there is not already a module with this name published
    // under the transaction sender's account.
    let module_id = compiled_module.self_id();
    if data_cache.exists_module(&module_id)? {
      let old_module_ref =
        self.loader
          .load_module_expect_not_missing(&module_id, data_cache, &log_context)?;
      let old_module = old_module_ref.module();
      let old_m = normalized::Module::new(old_module);
      let new_m = normalized::Module::new(&compiled_module);
      let compat = Compatibility::check(&old_m, &new_m);
      if !compat.is_fully_compatible() {
        return Err(
          PartialVMError::new(StatusCode::BACKWARD_INCOMPATIBLE_MODULE_UPDATE)
            .finish(Location::Undefined),
        );
      }
    }

    // perform bytecode and loading verification
    self.loader
      .verify_module_for_publication(&compiled_module, data_cache, &log_context)?;

    data_cache.publish_module(&module_id, module)
  }

  // pub fn execute_script<'vtxn>(
  //   &self,
  //   solver: &'ctx Solver<'ctx>,
  //   vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
  //   txn_data: &'vtxn TransactionMetadata,
  //   _gas_schedule: &CostTable,
  //   script: Vec<u8>,
  //   ty_args: Vec<TypeTag>,
  //   args: Vec<SymValue<'ctx>>,
  // ) -> PartialVMResult<()> {
  //   let mut type_params = vec![];
  //   for ty in &ty_args {
  //     type_params.push(self.loader.load_type(ty, vm_ctx)?);
  //   }
  //   let main = self.loader.load_script(&script, vm_ctx)?;

  //   self
  //     .loader
  //     .verify_ty_args(main.type_parameters(), &type_params)?;
  //   verify_args(main.parameters(), &args)?;

  //   SymInterpreter::entrypoint(
  //     solver,
  //     vm_ctx,
  //     &self.loader,
  //     txn_data,
  //     // gas_schedule,
  //     main,
  //     // type_params,
  //     args,
  //   )
  // }

  pub fn execute_function(
    &self,
    z3_ctx: &'ctx Context,
    plugin_manager: &PluginManager<'_>,
    // gas_schedule: &CostTable,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: Vec<TypeTag>,
    args: Vec<SymValue<'ctx>>,
    mut data_cache: SymDataCache<'ctx, '_, '_, impl RemoteCache>,
  ) -> VMResult<()> {
    let (func, ty_args, _params, _return_tys) = self.loader.load_function(
      function_name,
      module,
      &ty_args,
      false,
      &mut data_cache,
      &NoContextLog::new()
    )?;

    let args_cloned: PartialVMResult<Vec<_>> = args.iter().map(|v| v.copy_value()).collect();
    let args_cloned = args_cloned.map_err(|e| e.finish(Location::Undefined))?;

    let interp = SymInterpreter::entrypoint(
      z3_ctx,
      // gas_schedule,
      func,
      ty_args,
      args_cloned,
      data_cache,
    )?;

    let args: PartialVMResult<Vec<_>> = args.into_iter().map(|v| v.as_runtime_ast(self.ty_ctx())).collect();
    let args = args.map_err(|e| e.finish(Location::Undefined))?;

    let mut interp_stack = vec![];
    interp_stack.push(interp);
    loop {
      if let Some(interp) = interp_stack.pop() {
        match interp.execute(&self.loader, plugin_manager)? {
          SymInterpreterExecutionResult::Fork(forks) => {
            for result in forks {
              match result {
                SymInterpreterForkResult::Fork(interp) => interp_stack.push(interp),
                SymInterpreterForkResult::Aborted(mut interp, err) => {
                  plugin_manager.on_after_execute_abort(&mut interp, &err)?;
                  println!("-------REPORT BEGIN-------");
                  println!("Function aborted.");
                  println!("Error: {:?}", err);
                  println!("-------REPORT END---------");
                  println!();
                }
              }
            }
          }
          SymInterpreterExecutionResult::Report(report) => {
            match report {
              ExecutionReport::Returned(model, return_values, memory) => {
                println!("-------REPORT BEGIN-------");
                println!("Function returned without abortion.");
                println!("Args:");
                for (idx, val) in args.iter().enumerate() {
                  println!("Index {}: {:#?}", idx, model.eval(val, true));
                }
                println!("Returns:");
                for (idx, val) in return_values.into_iter().enumerate() {
                  let ast = val.as_runtime_ast(self.ty_ctx()).map_err(|e| e.finish(Location::Undefined))?;
                  println!("Index {}: {:#?}", idx, model.eval(&ast, true));
                }
                // println!("Memory:");
                // println!("{:?}", memory);
                println!("-------REPORT END---------");
                println!();
              },
              ExecutionReport::UserAborted(code) => {
                println!("-------REPORT BEGIN-------");
                println!("Function aborted by user.");
                println!("Code: {:?}", code);
                println!("-------REPORT END---------");
                println!();
              }
            }
          }
        }
      } else {
        break;
      }
    }
    Ok(())
  }

  pub(crate) fn load_function(
    &self,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: &[TypeTag],
    data_cache: &mut SymDataCache<'ctx, '_, '_, impl RemoteCache>,
  ) -> VMResult<(Arc<Function>, Vec<Type>, Vec<Type>, Vec<Type>)> {
    self.loader.load_function(
      function_name,
      module,
      ty_args,
      false,
      data_cache,
      &NoContextLog::new(),
    )
  }

  pub(crate) fn type_to_type_tag(&self, ty: &Type) -> PartialVMResult<TypeTag> {
    self.loader.type_to_type_tag(ty)
  }
}
