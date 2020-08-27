use crate::runtime::{interpreter::SymInterpreter, loader::Resolver};
use libra_types::{
  access_path::AccessPath, account_address::AccountAddress, account_config::CORE_CODE_ADDRESS,
  contract_event::ContractEvent,
};
use move_core_types::{/* gas_schedule::CostTable, */identifier::IdentStr, language_storage::ModuleId};
// use move_vm_natives::{account, event, hash, lcs, signature};
use move_vm_types::{
  loaded_data::{runtime_types::Type, types::FatType},
};
use crate::{
  state::vm_context::SymbolicVMContext,
  types::{
    natives::{SymNativeContext, SymNativeResult},
    values::{vector, SymStruct, SymValue},
  },
};
use std::{collections::VecDeque, fmt::Write};
use vm::errors::VMResult;
use z3::Context;

// The set of native functions the VM supports.
// The functions can line in any crate linked in but the VM declares them here.
// 2 functions have to be implemented for a `NativeFunction`:
// - `resolve` which given a function unique name ModuleAddress::ModuleName::FunctionName
// returns a `NativeFunction`
// - `dispatch` which given a `NativeFunction` invokes the native
#[derive(Debug, Clone, Copy)]
pub(crate) enum NativeFunction {
  HashSha2_256,
  HashSha3_256,
  LCSToBytes,
  PubED25519Validate,
  SigED25519Verify,
  SigED25519ThresholdVerify,
  VectorLength,
  VectorEmpty,
  VectorBorrow,
  VectorBorrowMut,
  VectorPushBack,
  VectorPopBack,
  VectorDestroyEmpty,
  VectorSwap,
  AccountWriteEvent,
  AccountSaveAccount,
  DebugPrint,
  DebugPrintStackTrace,
}

impl NativeFunction {
  pub(crate) fn resolve(
    module_address: &AccountAddress,
    module_name: &str,
    function_name: &str,
  ) -> Option<NativeFunction> {
    use NativeFunction::*;

    let case = (module_address, module_name, function_name);
    Some(match case {
      (&CORE_CODE_ADDRESS, "Hash", "sha2_256") => HashSha2_256,
      (&CORE_CODE_ADDRESS, "Hash", "sha3_256") => HashSha3_256,
      (&CORE_CODE_ADDRESS, "LCS", "to_bytes") => LCSToBytes,
      (&CORE_CODE_ADDRESS, "Signature", "ed25519_validate_pubkey") => PubED25519Validate,
      (&CORE_CODE_ADDRESS, "Signature", "ed25519_verify") => SigED25519Verify,
      (&CORE_CODE_ADDRESS, "Signature", "ed25519_threshold_verify") => SigED25519ThresholdVerify,
      (&CORE_CODE_ADDRESS, "Vector", "length") => VectorLength,
      (&CORE_CODE_ADDRESS, "Vector", "empty") => VectorEmpty,
      (&CORE_CODE_ADDRESS, "Vector", "borrow") => VectorBorrow,
      (&CORE_CODE_ADDRESS, "Vector", "borrow_mut") => VectorBorrowMut,
      (&CORE_CODE_ADDRESS, "Vector", "push_back") => VectorPushBack,
      (&CORE_CODE_ADDRESS, "Vector", "pop_back") => VectorPopBack,
      (&CORE_CODE_ADDRESS, "Vector", "destroy_empty") => VectorDestroyEmpty,
      (&CORE_CODE_ADDRESS, "Vector", "swap") => VectorSwap,
      (&CORE_CODE_ADDRESS, "Event", "write_to_event_store") => AccountWriteEvent,
      (&CORE_CODE_ADDRESS, "LibraAccount", "save_account") => AccountSaveAccount,
      (&CORE_CODE_ADDRESS, "Debug", "print") => DebugPrint,
      (&CORE_CODE_ADDRESS, "Debug", "print_stack_trace") => DebugPrintStackTrace,
      _ => return None,
    })
  }

  /// Given the vector of aguments, it executes the native function.
  pub(crate) fn dispatch<'ctx>(
    self,
    ctx: &mut impl SymNativeContext<'ctx>,
    t: Vec<Type>,
    v: VecDeque<SymValue<'ctx>>,
  ) -> VMResult<SymNativeResult<'ctx>> {
    match self {
      // Self::HashSha2_256 => hash::native_sha2_256(ctx, t, v),
      // Self::HashSha3_256 => hash::native_sha3_256(ctx, t, v),
      // Self::PubED25519Validate => signature::native_ed25519_publickey_validation(ctx, t, v),
      // Self::SigED25519Verify => signature::native_ed25519_signature_verification(ctx, t, v),
      // Self::SigED25519ThresholdVerify => {
      //   signature::native_ed25519_threshold_signature_verification(ctx, t, v)
      // }
      Self::VectorLength => vector::native_length(ctx, t, v),
      Self::VectorEmpty => vector::native_empty(ctx, t, v),
      Self::VectorBorrow => vector::native_borrow(ctx, t, v),
      Self::VectorBorrowMut => vector::native_borrow(ctx, t, v),
      Self::VectorPushBack => vector::native_push_back(ctx, t, v),
      Self::VectorPopBack => vector::native_pop(ctx, t, v),
      Self::VectorDestroyEmpty => vector::native_destroy_empty(ctx, t, v),
      Self::VectorSwap => vector::native_swap(ctx, t, v),
      // natives that need the full API of `NativeContext`
      // Self::AccountWriteEvent => event::native_emit_event(ctx, t, v),
      // Self::AccountSaveAccount => account::native_save_account(ctx, t, v),
      // Self::LCSToBytes => lcs::native_to_bytes(ctx, t, v),
      // Self::DebugPrint => debug::native_print(ctx, t, v),
      // Self::DebugPrintStackTrace => debug::native_print_stack_trace(ctx, t, v),
      _ => unimplemented!(),
    }
  }
}

pub(crate) struct SymFunctionContext<'a, 'vtxn, 'ctx> {
  z3_ctx: &'ctx Context,
  interpreter: &'a mut SymInterpreter<'vtxn, 'ctx>,
  vm_ctx: &'a mut SymbolicVMContext<'vtxn, 'ctx>,
  resolver: &'a Resolver<'a>,
}

impl<'a, 'vtxn, 'ctx> SymFunctionContext<'a, 'vtxn, 'ctx> {
  pub(crate) fn new(
    z3_ctx: &'ctx Context,
    interpreter: &'a mut SymInterpreter<'vtxn, 'ctx>,
    vm_ctx: &'a mut SymbolicVMContext<'vtxn, 'ctx>,
    resolver: &'a Resolver<'a>,
  ) -> SymFunctionContext<'a, 'vtxn, 'ctx> {
    SymFunctionContext {
      z3_ctx,
      interpreter,
      vm_ctx,
      resolver,
    }
  }
}

impl<'a, 'vtxn, 'ctx> SymNativeContext<'ctx> for SymFunctionContext<'a, 'vtxn, 'ctx> {
  fn get_z3_ctx(&self) -> &'ctx Context {
    self.z3_ctx
  }

  fn print_stack_trace<B: Write>(&self, _buf: &mut B) -> VMResult<()> {
    // self
    //   .interpreter
    //   .debug_print_stack_trace(buf, &self.resolver)
    Ok(())
  }

  // fn cost_table(&self) -> &CostTable {
  //   self.interpreter.gas_schedule()
  // }

  fn save_under_address(
    &mut self,
    ty_args: &[Type],
    module_id: &ModuleId,
    struct_name: &IdentStr,
    resource_to_save: SymStruct<'ctx>,
    account_address: AccountAddress,
  ) -> VMResult<()> {
    let libra_type = self.resolver.get_libra_type_info(
      module_id,
      struct_name,
      ty_args,
      self.vm_ctx,
    )?;
    let ap = AccessPath::new(account_address, libra_type.resource_key().to_vec());
    self
      .interpreter.state
      .move_resource_to(self.vm_ctx, &ap, libra_type.fat_type(), resource_to_save)
  }

  fn save_event(&mut self, event: ContractEvent) -> VMResult<()> {
    Ok(self.interpreter.state.push_event(event))
  }

  fn convert_to_fat_types(&self, types: Vec<Type>) -> VMResult<Vec<FatType>> {
    types
      .iter()
      .map(|ty| self.resolver.type_to_fat_type(ty))
      .collect()
  }
}
