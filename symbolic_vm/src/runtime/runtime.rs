use bytecode_verifier::VerifiedModule;
// use libra_logger::prelude::*;
use libra_types::vm_error::{StatusCode, VMStatus};
use move_core_types::{
  // gas_schedule::CostTable,
  identifier::{IdentStr, Identifier},
  language_storage::{ModuleId, TypeTag},
};
use move_vm_types::{
  transaction_metadata::TransactionMetadata,
};
use crate::{
  runtime::{interpreter::{SymInterpreter, SymInterpreterExecutionResult}, loader::Loader},
  state::vm_context::SymbolicVMContext,
};
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

use z3::{Context, ast::{Ast, BV, Bool}};
use crate::{
  plugin::{PluginManager, IntegerArithmeticPlugin, VerificationPlugin, Specification},
  types::values::{SymValue, SymBool, SymU64, VMSymValueCast, SymbolicMoveValue},
  runtime::loader::Function,
};

/// An instantiation of the MoveVM.
pub(crate) struct VMRuntime<'ctx> {
  loader: Loader,

  phatom: PhantomData<&'ctx Context>,
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
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
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
    if vm_ctx.exists_module(&module_id) {
      return Err(vm_error(
        Location::default(),
        StatusCode::DUPLICATE_MODULE_NAME,
      ));
    };

    let verified_module = VerifiedModule::new(compiled_module).map_err(|(_, e)| e)?;
    Loader::check_natives(&verified_module)?;
    vm_ctx.publish_module(module_id, module)
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
  // ) -> VMResult<()> {
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

  pub fn execute_function<'vtxn>(
    &self,
    z3_ctx: &'ctx Context,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    // gas_schedule: &CostTable,
    module: &ModuleId,
    function_name: &IdentStr,
    ty_args: Vec<TypeTag>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let int_plugin = IntegerArithmeticPlugin::new();
    let target_spec = Specification::new(
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true),
      |_a: &[SymValue<'ctx>], _r: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true),
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true)
    );
    let abs_spec = Specification::new(
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true),
      |_a: &[SymValue<'ctx>], r: &[SymValue<'ctx>]| {
        // !!! bad type conversions and clones
        // !!! figure it out
        let ret = VMSymValueCast::<SymU64<'ctx>>::cast(r[0].copy_value()).unwrap();
        SymBool::from_ast(ret.as_inner().bvuge(&BV::from_u64(z3_ctx, 10, 64)))
      },
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true)
    );
    let abs_spec_right = Specification::new(
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true),
      |a: &[SymValue<'ctx>], r: &[SymValue<'ctx>]| {
        // !!! bad type conversions and clones
        // !!! figure it out
        let arg = VMSymValueCast::<SymU64<'ctx>>::cast(a[0].copy_value()).unwrap();
        let ret = VMSymValueCast::<SymU64<'ctx>>::cast(r[0].copy_value()).unwrap();
        let const_ten = BV::from_u64(z3_ctx, 10, 64);
        let arg_ast = arg.as_inner();
        let ret_ast = ret.as_inner();
        let cond_pos = arg_ast.bvuge(&const_ten).implies(&ret_ast._eq(&arg_ast));
        let cond_neg = arg_ast.bvult(&const_ten).implies(&ret_ast._eq(&const_ten.bvsub(&arg_ast)));
        let cond = Bool::and(z3_ctx, &[&cond_pos, &cond_neg]);
        SymBool::from_ast(cond)
      },
      |_a: &[SymValue<'ctx>]| SymBool::from(z3_ctx, true)
    );
    let mut verification_plugin = VerificationPlugin::new(target_spec);
    let func_name = Identifier::new("abs_on_ten").unwrap();
    verification_plugin.add_spec(func_name, abs_spec_right);
    let mut manager = PluginManager::new();
    manager.add_plugin(int_plugin);
    manager.add_plugin(verification_plugin);
  
    let mut type_params = vec![];
    for ty in &ty_args {
      type_params.push(self.loader.load_type(ty, vm_ctx)?);
    }
    let func = self.loader.load_function(function_name, module, vm_ctx)?;

    // self
    //   .loader
    //   .verify_ty_args(func.type_parameters(), &type_params)?;
    // REVIEW: argument verification should happen in the interpreter
    // verify_args(func.parameters(), &args)?;

    let interp = SymInterpreter::entrypoint(
      z3_ctx,
      vm_ctx,
      txn_data,
      // gas_schedule,
      func,
      type_params,
      &args,
    )?;

    let args: VMResult<Vec<_>> = args.into_iter().map(|v| v.as_ast()).collect();
    let args = args?;

    let mut interp_stack = vec![];
    interp_stack.push(interp);
    loop {
      if let Some(interp) = interp_stack.pop() {
        match interp.execute(&self.loader, vm_ctx, &mut manager)? {
          SymInterpreterExecutionResult::Fork(forks) => {
            for interp in forks {
              interp_stack.push(interp);
            }
          }
          SymInterpreterExecutionResult::Report(model, return_values) => {
            println!("---------------------");
            println!("Args:");
            for (idx, val) in args.iter().enumerate() {
              println!("Index {}: {:#?}", idx, model.eval(val));
            }
            println!("Returns:");
            for (idx, val) in return_values.into_iter().enumerate() {
              println!("Index {}: {:#?}", idx, model.eval(&val.as_ast()?));
            }
            println!("---------------------");
          }
        }
      } else {
        break;
      }
    }
    Ok(())
  }

  pub fn cache_module(
    &self,
    module: VerifiedModule,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
  ) -> VMResult<()> {
    self.loader.cache_module(module, vm_ctx)
  }

  pub fn load_function(
    &self,
    function_name: &IdentStr,
    module_id: &ModuleId,
    vm_ctx: &mut SymbolicVMContext<'_, 'ctx>,
  ) -> VMResult<Arc<Function>> {
    self.loader.load_function(function_name, module_id, vm_ctx)
  }
}

/// Verify if the transaction arguments match the type signature of the main function.
fn _verify_args<'ctx>(signature: &Signature, args: &[SymValue<'ctx>]) -> VMResult<()> {
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
