use crate::runtime::{interpreter::SymInterpreter, loader::Loader};
use bytecode_verifier::VerifiedModule;
// use libra_logger::prelude::*;
use libra_types::vm_error::{StatusCode, VMStatus};
use move_core_types::{
  gas_schedule::CostTable,
  identifier::IdentStr,
  language_storage::{ModuleId, TypeTag},
};
use move_vm_types::{
  transaction_metadata::TransactionMetadata,
};
use crate::types::interpreter_context::SymInterpreterContext;

use vm::{
  access::ModuleAccess,
  errors::{verification_error, vm_error, Location, VMResult},
  file_format::Signature,
  CompiledModule, IndexKind,
};

use std::{
  marker::PhantomData,
  sync::Arc,
};

use solver::Solver;
use crate::{
  types::values::SymValue,
  runtime::loader::Function,
};

/// An instantiation of the MoveVM.
pub(crate) struct VMRuntime<'ctx> {
  loader: Loader,

  phatom: PhantomData<&'ctx Solver<'ctx>>,
}

impl<'ctx> VMRuntime<'ctx> {
  pub fn new() -> Self {
    VMRuntime {
      loader: Loader::new(),
      phatom: PhantomData,
    }
  }

  pub(crate) fn publish_module(
    &self,
    module: Vec<u8>,
    context: &mut dyn SymInterpreterContext,
    txn_data: &TransactionMetadata,
  ) -> VMResult<()> {
    let compiled_module = match CompiledModule::deserialize(&module) {
      Ok(module) => module,
      Err(err) => {
        // warn!("[VM] module deserialization failed {:?}", err);
        return Err(err);
      }
    };

    // Make sure the module's self address matches the transaction sender. The self address is
    // where the module will actually be published. If we did not check this, the sender could
    // publish a module under anyone's account.
    if compiled_module.address() != &txn_data.sender {
      return Err(verification_error(
        IndexKind::AddressIdentifier,
        compiled_module.self_handle_idx().0 as usize,
        StatusCode::MODULE_ADDRESS_DOES_NOT_MATCH_SENDER,
      ));
    }

    // Make sure that there is not already a module with this name published
    // under the transaction sender's account.
    let module_id = compiled_module.self_id();
    if context.exists_module(&module_id) {
      return Err(vm_error(
        Location::default(),
        StatusCode::DUPLICATE_MODULE_NAME,
      ));
    };

    let verified_module = VerifiedModule::new(compiled_module).map_err(|(_, e)| e)?;
    Loader::check_natives(&verified_module)?;
    context.publish_module(module_id, module)
  }

  pub fn execute_script(
    &self,
    solver: &'ctx Solver<'ctx>,
    context: &mut dyn SymInterpreterContext,
    txn_data: &TransactionMetadata,
    gas_schedule: &CostTable,
    script: Vec<u8>,
    ty_args: Vec<TypeTag>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let mut type_params = vec![];
    for ty in &ty_args {
      type_params.push(self.loader.load_type(ty, context)?);
    }
    let main = self.loader.load_script(&script, context)?;

    self
      .loader
      .verify_ty_args(main.type_parameters(), &type_params)?;
    verify_args(main.parameters(), &args)?;

    SymInterpreter::entrypoint(
      solver,
      context,
      &self.loader,
      txn_data,
      // gas_schedule,
      main,
      // type_params,
      args,
    )
  }

  pub fn execute_function(
    &self,
    solver: &'ctx Solver<'ctx>,
    context: &mut dyn SymInterpreterContext,
    txn_data: &TransactionMetadata,
    // gas_schedule: &CostTable,
    module: &ModuleId,
    function_name: &IdentStr,
    // ty_args: Vec<TypeTag>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    // let mut type_params = vec![];
    // for ty in &ty_args {
    //   type_params.push(self.loader.load_type(ty, context)?);
    // }
    let func = self.loader.load_function(function_name, module, context)?;

    // self
    //   .loader
    //   .verify_ty_args(func.type_parameters(), &type_params)?;
    // REVIEW: argument verification should happen in the interpreter
    //verify_args(func.parameters(), &args)?;

    SymInterpreter::entrypoint(
      solver,
      context,
      &self.loader,
      txn_data,
      // gas_schedule,
      func,
      // type_params,
      args,
    )
  }

  pub fn cache_module(
    &self,
    module: VerifiedModule,
    context: &mut dyn SymInterpreterContext,
  ) -> VMResult<()> {
    self.loader.cache_module(module, context)
  }

  pub fn load_function(
    &self,
    function_name: &IdentStr,
    module_id: &ModuleId,
    context: &mut dyn SymInterpreterContext,
  ) -> VMResult<Arc<Function>> {
    self.loader.load_function(function_name, module_id, context)
  }
}

/// Verify if the transaction arguments match the type signature of the main function.
fn verify_args<'ctx>(signature: &Signature, args: &[SymValue<'ctx>]) -> VMResult<()> {
  if signature.len() != args.len() {
    return Err(
      VMStatus::new(StatusCode::TYPE_MISMATCH).with_message(format!(
        "argument length mismatch: expected {} got {}",
        signature.len(),
        args.len()
      )),
    );
  }
  for (tok, val) in signature.0.iter().zip(args) {
    if !val.is_valid_script_arg(tok) {
      return Err(
        VMStatus::new(StatusCode::TYPE_MISMATCH).with_message("argument type mismatch".to_string()),
      );
    }
  }
  Ok(())
}
