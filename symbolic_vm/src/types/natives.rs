//! Native Function Support
//!
//! All move native functions have the following signature:
//!
//! `pub fn native_function<'ctx>(
//!     context: &mut impl SymNativeContext<'ctx>,
//!     ty_args: Vec<Type>,
//!     mut arguments: VecDeque<SymValue<'ctx>>,
//! ) -> PartialVMResult<SymNativeResult<'ctx>>;`
//!
//! arguments are passed with first argument at position 0 and so forth.
//! Popping values from `arguments` gives the aguments in reverse order (last first).
//! This module contains the declarations and utilities to implement a native
//! function.

use move_core_types::{
  gas_schedule::{AbstractMemorySize, CostTable, GasAlgebra, GasCarrier, InternalGasUnits},
  language_storage::TypeTag,
  value::MoveTypeLayout,
};
use move_vm_types::{
  gas_schedule::NativeCostIndex,
  loaded_data::runtime_types::Type,
};
use std::fmt::Write;
use vm::errors::PartialVMResult;

use crate::types::values::SymValue;
use z3::Context;

pub use move_core_types::vm_status::StatusCode;
pub use vm::errors::PartialVMError;

/// `SymNativeContext` - Symbolic Native function context.
///
/// This is the API, the "privileges", a native function is given.
/// Normally a native function will only need the `CostTable`.
/// The set of native functions and their linkage is entirely inside the MoveVM
/// runtime.
pub trait SymNativeContext<'ctx> {
  /// Returns Z3 context
  fn get_z3_ctx(&self) -> &'ctx Context;
  /// Prints stack trace.
  fn print_stack_trace<B: Write>(&self, buf: &mut B) -> PartialVMResult<()>;
  /// Gets cost table ref.
  // fn cost_table(&self) -> &CostTable;
  /// Saves contract event. Returns true if successful
  fn save_event(
    &mut self,
    guid: Vec<u8>,
    count: u64,
    ty: Type,
    val: SymValue<'ctx>,
  ) -> PartialVMResult<bool>;
  /// Get the a type tag via the type.
  fn type_to_type_tag(&self, ty: &Type) -> PartialVMResult<Option<TypeTag>>;
  /// Get the a data layout via the type.
  fn type_to_type_layout(&self, ty: &Type) -> PartialVMResult<Option<MoveTypeLayout>>;
}

/// Result of a symbolic native function execution requires charges for execution cost.
///
/// An execution that causes an invariant violation would not return a `SymNativeResult` but
/// return a `VMResult` error directly.
/// All native functions must return a `VMResult<SymNativeResult>` where an `Err` is returned
/// when an error condition is met that should not charge for the execution. A common example
/// is a VM invariant violation which should have been forbidden by the verifier.
/// Errors (typically user errors and aborts) that are logically part of the function execution
/// must be expressed in a `NativeResult` with a cost and a VMStatus.
pub struct SymNativeResult<'ctx> {
  /// The cost for running that function, whether successfully or not.
  pub cost: InternalGasUnits<GasCarrier>,
  /// Result of execution. This is either the return values or the error to report.
  pub result: Result<Vec<SymValue<'ctx>>, u64>,
}

impl<'ctx> SymNativeResult<'ctx> {
  /// Return values of a successful execution.
  pub fn ok(cost: InternalGasUnits<GasCarrier>, values: Vec<SymValue<'ctx>>) -> Self {
    SymNativeResult {
      cost,
      result: Ok(values),
    }
  }

  /// `VMStatus` of a failed execution. The failure is a runtime failure in the function
  /// and not an invariant failure of the VM which would raise a `VMResult` error directly.
  pub fn err(cost: InternalGasUnits<GasCarrier>, abort_code: u64) -> Self {
    SymNativeResult {
      cost,
      result: Err(abort_code),
    }
  }
}

/// Return the native gas entry in `CostTable` for the given key.
/// The key is the specific native function index known to `CostTable`.
pub fn native_gas(
  table: &CostTable,
  key: NativeCostIndex,
  size: usize,
) -> InternalGasUnits<GasCarrier> {
  let gas_amt = table.native_cost(key as u8);
  let memory_size = AbstractMemorySize::new(std::cmp::max(1, size) as GasCarrier);
  debug_assert!(memory_size.get() > 0);
  gas_amt.total().mul(memory_size)
}

/// Return the argument at the top of the stack.
///
/// Arguments are passed to a native as a stack with first arg at the bottom of the stack.
/// Calling this API can help in making the code more readable.
/// It's good practice to pop all arguments in locals of the native function on function entry.
#[macro_export]
macro_rules! pop_arg {
  ($arguments:ident, $t:ty) => {{
    use $crate::types::natives::{PartialVMError, StatusCode};
    match $arguments.pop_back().map(|v| v.value_as::<$t>()) {
      None => {
        return Err(PartialVMError::new(
          StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR,
        ))
      }
      Some(Err(e)) => return Err(e),
      Some(Ok(v)) => v,
    }
  }};
}
