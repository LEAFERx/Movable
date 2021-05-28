use crate::runtime::{interpreter::SymInterpreter, loader::Resolver};
use diem_types::{
  account_address::AccountAddress, account_config::CORE_CODE_ADDRESS,
};
use move_core_types::{
  gas_schedule::{InternalGasUnits, GasAlgebra},
  language_storage::TypeTag,
  value::MoveTypeLayout, vm_status::StatusType,
};
// use move_vm_natives::{account, event, hash, lcs, signature};
use crate::{
  natives::{account, signer, vector},
  types::{
    data_store::SymDataStore,
    natives::{SymNativeContext, SymNativeResult},
    values::SymValue,
  },
};
use move_vm_types::{
  loaded_data::runtime_types::Type,
};
use move_vm_runtime::data_cache::RemoteCache;
use std::{collections::VecDeque, fmt::Write};
use vm::errors::PartialVMResult;
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
  BCSToBytes,
  PubED25519Validate,
  SigED25519Verify,
  VectorLength,
  VectorEmpty,
  VectorBorrow,
  VectorBorrowMut,
  VectorPushBack,
  VectorPopBack,
  VectorDestroyEmpty,
  VectorSwap,
  AccountWriteEvent,
  DebugPrint,
  DebugPrintStackTrace,
  SignerBorrowAddress,
  CreateSigner,
  DestroySigner,
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
      (&CORE_CODE_ADDRESS, "BCS", "to_bytes") => BCSToBytes,
      (&CORE_CODE_ADDRESS, "Signature", "ed25519_validate_pubkey") => PubED25519Validate,
      (&CORE_CODE_ADDRESS, "Signature", "ed25519_verify") => SigED25519Verify,
      (&CORE_CODE_ADDRESS, "Vector", "length") => VectorLength,
      (&CORE_CODE_ADDRESS, "Vector", "empty") => VectorEmpty,
      (&CORE_CODE_ADDRESS, "Vector", "borrow") => VectorBorrow,
      (&CORE_CODE_ADDRESS, "Vector", "borrow_mut") => VectorBorrowMut,
      (&CORE_CODE_ADDRESS, "Vector", "push_back") => VectorPushBack,
      (&CORE_CODE_ADDRESS, "Vector", "pop_back") => VectorPopBack,
      (&CORE_CODE_ADDRESS, "Vector", "destroy_empty") => VectorDestroyEmpty,
      (&CORE_CODE_ADDRESS, "Vector", "swap") => VectorSwap,
      (&CORE_CODE_ADDRESS, "Event", "write_to_event_store") => AccountWriteEvent,
      (&CORE_CODE_ADDRESS, "DiemAccount", "create_signer") => CreateSigner,
      (&CORE_CODE_ADDRESS, "DiemAccount", "destroy_signer") => DestroySigner,
      (&CORE_CODE_ADDRESS, "Debug", "print") => DebugPrint,
      (&CORE_CODE_ADDRESS, "Debug", "print_stack_trace") => DebugPrintStackTrace,
      (&CORE_CODE_ADDRESS, "Signer", "borrow_address") => SignerBorrowAddress,
      _ => return None,
    })
  }

  /// Given the vector of aguments, it executes the native function.
  pub(crate) fn dispatch<'ctx>(
    self,
    ctx: &mut impl SymNativeContext<'ctx>,
    t: Vec<Type>,
    v: VecDeque<SymValue<'ctx>>,
  ) -> PartialVMResult<SymNativeResult<'ctx>> {
    let result = match self {
      // Self::HashSha2_256 => hash::native_sha2_256(ctx, t, v),
      // Self::HashSha3_256 => hash::native_sha3_256(ctx, t, v),
      // Self::PubED25519Validate => signature::native_ed25519_publickey_validation(ctx, t, v),
      // Self::SigED25519Verify => signature::native_ed25519_signature_verification(ctx, t, v),
      Self::VectorLength => vector::native_length(ctx, t, v),
      Self::VectorEmpty => vector::native_empty(ctx, t, v),
      Self::VectorBorrow => vector::native_borrow(ctx, t, v),
      Self::VectorBorrowMut => vector::native_borrow(ctx, t, v),
      Self::VectorPushBack => vector::native_push_back(ctx, t, v),
      Self::VectorPopBack => vector::native_pop(ctx, t, v),
      Self::VectorDestroyEmpty => vector::native_destroy_empty(ctx, t, v),
      Self::VectorSwap => vector::native_swap(ctx, t, v),
      // // natives that need the full API of `NativeContext`
      // Self::AccountWriteEvent => event::native_emit_event(ctx, t, v),
      // Self::BCSToBytes => bcs::native_to_bytes(ctx, t, v),
      // Self::DebugPrint => debug::native_print(ctx, t, v),
      // Self::DebugPrintStackTrace => debug::native_print_stack_trace(ctx, t, v),
      Self::SignerBorrowAddress => signer::native_borrow_address(ctx, t, v),
      Self::CreateSigner => account::native_create_signer(ctx, t, v),
      Self::DestroySigner => account::native_destroy_signer(ctx, t, v),
      _ => Ok(SymNativeResult::ok(InternalGasUnits::new(0), vec![]))
    };
    debug_assert!(match &result {
      Err(e) => e.major_status().status_type() == StatusType::InvariantViolation,
      Ok(_) => true,
    });
    result
  }
}

pub(crate) struct SymFunctionContext<'a, 'ctx, 'r, 'l, R> {
  z3_ctx: &'ctx Context,
  interpreter: &'a mut SymInterpreter<'ctx, 'r, 'l, R>,
  // cost_strategy: &'a ...
  resolver: &'a Resolver<'l>,
}

impl<'a, 'ctx, 'r, 'l, R: RemoteCache> SymFunctionContext<'a, 'ctx, 'r, 'l, R> {
  pub(crate) fn new(
    interpreter: &'a mut SymInterpreter<'ctx, 'r, 'l, R>,
    resolver: &'a Resolver<'l>,
  ) -> Self {
    SymFunctionContext {
      z3_ctx: interpreter.data_cache().get_z3_ctx(),
      interpreter,
      resolver,
    }
  }
}

impl<'a, 'ctx, 'r, 'l, R: RemoteCache> SymNativeContext<'ctx> for SymFunctionContext<'a, 'ctx, 'r, 'l, R> {
  fn get_z3_ctx(&self) -> &'ctx Context {
    self.z3_ctx
  }

  fn print_stack_trace<B: Write>(&self, _buf: &mut B) -> PartialVMResult<()> {
    // self
    //   .interpreter
    //   .debug_print_stack_trace(buf, &self.resolver)
    Ok(())
  }

  // fn cost_table(&self) -> &CostTable {
  //   self.interpreter.gas_schedule()
  // }

  fn save_event(
    &mut self,
    guid: Vec<u8>,
    seq_num: u64,
    ty: Type,
    val: SymValue<'ctx>,
  ) -> PartialVMResult<bool> {
    match self.interpreter.data_cache().emit_event(guid, seq_num, ty, val) {
      Ok(()) => Ok(true),
      Err(e) if e.major_status().status_type() == StatusType::InvariantViolation => Err(e),
      Err(_) => Ok(false),
    }
  }

  fn type_to_type_layout(&self, ty: &Type) -> PartialVMResult<Option<MoveTypeLayout>> {
    match self.resolver.type_to_type_layout(ty) {
      Ok(ty_layout) => Ok(Some(ty_layout)),
      Err(e) if e.major_status().status_type() == StatusType::InvariantViolation => Err(e),
      Err(_) => Ok(None),
    }
  }

  fn type_to_type_tag(&self, ty: &Type) -> PartialVMResult<Option<TypeTag>> {
    match self.resolver.type_to_type_tag(ty) {
      Ok(ty_tag) => Ok(Some(ty_tag)),
      Err(e) if e.major_status().status_type() == StatusType::InvariantViolation => Err(e),
      Err(_) => Ok(None),
    }
  }
}
