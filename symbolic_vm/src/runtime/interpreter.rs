// use move_vm_runtime::{
//   gas,
//   loader::{Function, Loader, Resolver},
//   native_functions::FunctionContext,
//   trace,
// };
use crate::runtime::{
  loader::{Function, Loader, Resolver},
  // native_functions::FunctionContext,
};
use libra_logger::prelude::*;
use libra_types::{
  access_path::AccessPath,
  account_address::AccountAddress,
  // transaction::MAX_TRANSACTION_SIZE_IN_BYTES,
  vm_error::{StatusCode, StatusType, VMStatus},
};
use move_core_types::gas_schedule::{AbstractMemorySize, /* CostTable, GasAlgebra, */ GasCarrier};
use move_vm_types::{
  // gas_schedule::calculate_intrinsic_gas,
  loaded_data::{runtime_types::Type, types::FatStructType},
  transaction_metadata::TransactionMetadata,
  // values::{self, SymIntegerValue, SymLocals, SymReference, Struct, StructRef, VMValueCast, SymValue},
};
use crate::{
  plugin::{
    IntegerArithmeticPlugin,
    PluginManager,
  },
  state::{
    interpreter_state::SymInterpreterState,
    vm_context::SymbolicVMContext,
  },
  types::{
    values::{
      SymU8, SymU64, /* SymU128, */ SymBool, SymAccountAddress, /* SymGlobalValue, */
      SymIntegerValue, SymLocals, SymReference, SymStruct, SymStructRef, SymValue, VMSymValueCast,
    },
  },
};

use nix::unistd::{fork, ForkResult};

use std::{
  // cmp::min,
  // collections::VecDeque,
  // fmt::Write,
  sync::Arc,
  // marker::PhantomData,
  process::exit,
};
use vm::{
  errors::*,
  file_format::{
    Bytecode, CodeOffset, FunctionHandleIndex, FunctionInstantiationIndex, StructDefInstantiationIndex,
    StructDefinitionIndex,
  },
  // file_format_common::Opcodes,
};

use z3::{Context, Solver, SatResult, Model};

// macro_rules! debug_write {
//   ($($toks: tt)*) => {
//       write!($($toks)*).map_err(|_|
//           VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//               .with_message("failed to write to buffer".to_string())
//       )
//   };
// }

// macro_rules! debug_writeln {
//   ($($toks: tt)*) => {
//       writeln!($($toks)*).map_err(|_|
//           VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//               .with_message("failed to write to buffer".to_string())
//       )
//   };
// }

/// `Interpreter` instances can execute Move functions.
///
/// An `Interpreter` instance is a stand alone execution context for a function.
/// It mimics execution on a single thread, with an call stack and an operand stack.
/// The `Interpreter` receives a reference to a data store used by certain opcodes
/// to do operations on data on chain and a `TransactionMetadata` which is also used to resolve
/// specific opcodes.

//??? pub(crate)
pub struct SymInterpreter<'vtxn, 'ctx> {
  /// Operand stack, where Move `SymValue`s are stored for stack operations.
  pub operand_stack: SymStack<'ctx>, //??? should not be pub
  /// The stack of active functions.
  call_stack: SymCallStack<'ctx>,
  /// Transaction data to resolve special bytecodes (e.g. GetTxnSequenceNumber, GetTxnPublicKey,
  /// GetTxnSenderAddress, ...)
  txn_data: &'vtxn TransactionMetadata,
  // gas_schedule: &'vtxn CostTable,
  /// Z3 solver
  pub solver: Solver<'ctx>,
  /// Intermediate state
  state: SymInterpreterState<'ctx>, 
}

impl<'vtxn, 'ctx> SymInterpreter<'vtxn, 'ctx> {
  /// Entrypoint into the interpreter. All external calls need to be routed through this
  /// function.
  pub(crate) fn entrypoint(
    z3_ctx: &'ctx Context,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    // gas_schedule: &'vtxn CostTable,
    function: Arc<Function>,
    ty_args: Vec<Type>,
    args: &Vec<SymValue<'ctx>>,
  ) -> VMResult<Self> {
    // We charge an intrinsic amount of gas based upon the size of the transaction submitted
    // (in raw bytes).
    // let txn_size = txn_data.transaction_size();
    // The callers of this function verify the transaction before executing it. Transaction
    // verification ensures the following condition.
    // TODO: This is enforced by Libra but needs to be enforced by other callers of the Move VM
    // as well.
    // assume!(txn_size.get() <= (MAX_TRANSACTION_SIZE_IN_BYTES as u64));
    // We count the intrinsic cost of the transaction here, since that needs to also cover the
    // setup of the function.
    // let mut interp = Self::new(txn_data, gas_schedule);
    let mut interp = Self::new(z3_ctx, vm_ctx, txn_data);
    // gas!(
    //   consume: context,
    //   calculate_intrinsic_gas(txn_size, &gas_schedule.gas_constants)
    // )?;
    
    let mut locals = SymLocals::new(z3_ctx, function.local_count());
    // TODO: assert consistency of args and function formals
    for (i, value) in args.iter().enumerate() {
      locals.store_loc(i, value.copy_value())?;
    }
    let current_frame = SymFrame::new(function, ty_args, locals);
    interp.call_stack.push(current_frame).or_else(|frame| {
      let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
      Err(interp.maybe_core_dump(err, &frame))
    })?;
    Ok(interp)
  }

  /// Create a new instance of an `Interpreter` in the context of a transaction with a
  /// given module cache and gas schedule.
  fn new(
    z3_ctx: &'ctx Context,
    vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    txn_data: &'vtxn TransactionMetadata,
    // gas_schedule: &'vtxn CostTable,
  ) -> Self {
    SymInterpreter {
      operand_stack: SymStack::new(),
      call_stack: SymCallStack::new(),
      // gas_schedule,
      txn_data,
      solver: Solver::new(&z3_ctx),
      state: vm_ctx.create_intermediate_state(),
    }
  }

  fn fork(&self) -> Self {
    SymInterpreter {
      operand_stack: self.operand_stack.clone(),
      call_stack: self.call_stack.clone(),
      txn_data: self.txn_data,
      solver: self.solver.translate(self.solver.get_context()),
      state: self.state.clone(),
    }
  }

  // pub(crate) fn gas_schedule(&self) -> &CostTable {
  //   self.gas_schedule
  // }

  /// Continue to execute
  pub fn execute(
    mut self,
    loader: &Loader,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    manager: &mut PluginManager,
  ) -> VMResult<SymInterpreterExecutionResult<'vtxn, 'ctx>> {
    if let Some(mut current_frame) = self.call_stack.pop() {
      loop {
        let resolver = current_frame.resolver(loader);
        let exit_code = current_frame
          .execute_code(&resolver, &mut self, vm_ctx, manager)
          .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
        match exit_code {
          ExitCode::Return => {
            if let Some(frame) = self.call_stack.pop() {
              current_frame = frame;
            } else {
              // Ok we have touched the end of the path, now let's report
              println!("Path explored: {:?}", self.solver);
              let mut return_values = vec![];
              for _ in 0..current_frame.function.return_count() {
                return_values.push(self.operand_stack.pop()?);
              }
              return Ok(SymInterpreterExecutionResult::Report(self.solver.get_model(), return_values));
            }
          }
          ExitCode::Call(fh_idx) => {
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::CALL,
            //   AbstractMemorySize::new(1 as GasCarrier)
            // )?;
            let func = resolver.function_at(fh_idx);
            if func.is_native() {
              // self.call_native(&resolver, context, func, vec![])?;
              continue;
            }
            // TODO: when a native function is executed, the current frame has not yet
            // been pushed onto the call stack. Fix it.
            let frame = self
              .make_call_frame(self.solver.get_context(), func, vec![])
              .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
            self.call_stack.push(current_frame).or_else(|frame| {
              let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
              Err(self.maybe_core_dump(err, &frame))
            })?;
            current_frame = frame;
          }
          ExitCode::CallGeneric(idx) => {
            let func_inst = resolver.function_instantiation_at(idx);
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::CALL_GENERIC,
            //   AbstractMemorySize::new((func_inst.instantiation_size() + 1) as GasCarrier)
            // )?;
            let func = loader.function_at(func_inst.handle());
            let ty_args = func_inst.materialize(current_frame.ty_args())?;
            if func.is_native() {
              // self.call_native(&resolver, context, func, ty_args)?;
              continue;
            }
            // TODO: when a native function is executed, the current frame has not yet
            // been pushed onto the call stack. Fix it.
            let frame = self
              .make_call_frame(self.solver.get_context(), func, ty_args)
              .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
            self.call_stack.push(current_frame).or_else(|frame| {
              let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
              Err(self.maybe_core_dump(err, &frame))
            })?;
            current_frame = frame;
          }
          ExitCode::Branch(instr, condition, offset) => {
            println!(
              "Hit Br{{{:?}}} instr, condition is {:?}, target offset is {:?}",
              instr,
              condition,
              offset,
            );

            let mut forks = vec![];

            let mut forked_interp = self.fork();
            let mut forked_frame = current_frame.clone();

            if instr {
              current_frame.pc = offset;
            } else {
              forked_frame.pc = offset;
            }

            self.call_stack.push(current_frame).or_else(|frame| {
              let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
              Err(self.maybe_core_dump(err, &frame))
            })?;

            forked_interp.call_stack.push(forked_frame).or_else(|frame| {
              let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
              Err(self.maybe_core_dump(err, &frame))
            })?;

            self.solver.assert(&condition.as_inner());
            if self.solver.check() == SatResult::Sat {
              forks.push(self);
            }

            forked_interp.solver.assert(&condition.as_inner().not());
            if forked_interp.solver.check() == SatResult::Sat {
              forks.push(forked_interp);
            }
            return Ok(SymInterpreterExecutionResult::Fork(forks));
          }
        }
      }
    } else {
      Err(VMStatus::new(StatusCode::EMPTY_CALL_STACK).with_message("Execute on empty call stack!".to_string()))
    }
  }

  /// Main loop for the execution of a function.
  ///
  /// This function sets up a `SymFrame` and calls `execute_code_unit` to execute code of the
  /// function represented by the frame. Control comes back to this function on return or
  /// on call. When that happens the frame is changes to a new one (call) or to the one
  /// at the top of the stack (return). If the call stack is empty execution is completed.
  // REVIEW: create account will be removed in favor of a native function (no opcode) and
  // we can simplify this code quite a bit.
  fn _execute_main(
    &mut self,
    solver: &Solver<'ctx>,
    loader: &Loader,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    function: Arc<Function>,
    ty_args: Vec<Type>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let mut msg = String::from("\n-------------------------\n");

    let int_plugin = IntegerArithmeticPlugin::new();
    let mut manager = PluginManager::new();
    manager.add_plugin(int_plugin);
  
    let mut locals = SymLocals::new(solver.get_context(), function.local_count());
    // TODO: assert consistency of args and function formals
    for (i, value) in args.iter().enumerate() {
      locals.store_loc(i, value.copy_value())?;
    }
    let mut current_frame = SymFrame::new(function, ty_args, locals);
    loop {
      let resolver = current_frame.resolver(loader);
      let exit_code = current_frame //self
        .execute_code(&resolver, self, vm_ctx, &mut manager)
        .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
      match exit_code {
        ExitCode::Return => {
          if let Some(frame) = self.call_stack.pop() {
            current_frame = frame;
          } else {
            // return Ok(());
            break;
          }
        }
        ExitCode::Call(fh_idx) => {
          // gas!(
          //   instr: context,
          //   self,
          //   Opcodes::CALL,
          //   AbstractMemorySize::new(1 as GasCarrier)
          // )?;
          let func = resolver.function_at(fh_idx);
          if func.is_native() {
            // self.call_native(&resolver, context, func, vec![])?;
            continue;
          }
          // TODO: when a native function is executed, the current frame has not yet
          // been pushed onto the call stack. Fix it.
          let frame = self
            .make_call_frame(solver.get_context(), func, vec![])
            .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
          self.call_stack.push(current_frame).or_else(|frame| {
            let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
            Err(self.maybe_core_dump(err, &frame))
          })?;
          current_frame = frame;
        }
        ExitCode::Branch(instr, condition, offset) => {
          println!(
            "Hit Br{{{:?}}} instr, condition is {:?}, target offset is {:?}",
            instr,
            condition,
            offset,
          );
          // Temp use fork to explore all branch
          // Use task stack to implement DFS later
          match fork() {
            Ok(ForkResult::Parent { .. }) => {
              msg += &format!("Fork parent: assume {:?}->{:#?}\n", instr, condition);
              if instr {
                solver.assert(&condition.as_inner());
              } else {
                solver.assert(&condition.not().as_inner());
              }
              if solver.check() == SatResult::Unsat {
                msg += "Parent not satisfied, exit.\n";
                msg += "-------------------------\n";
                print!("{}", msg);
                exit(0);
              }
              current_frame.pc = offset;
            }
            Ok(ForkResult::Child) => {
              msg += &format!("Fork child: assume {:?}->{:#?}\n", !instr, condition);
              if instr {
                solver.assert(&condition.not().as_inner());
              } else {
                solver.assert(&condition.as_inner());
              }
              if solver.check() == SatResult::Unsat {
                msg += "Child not satisfied, exit.\n";
                msg += "-------------------------\n";
                print!("{}", msg);
                exit(0);
              }
            }
            Err(_) => {
              return Err(VMStatus::new(StatusCode::ABORTED).with_message("Unable to fork, abort.".to_string()));
            }
          }
        }
        ExitCode::CallGeneric(_) => unimplemented!(),
        // ExitCode::CallGeneric(idx) => {
        //   let func_inst = resolver.function_instantiation_at(idx);
        //   // gas!(
        //   //   instr: context,
        //   //   self,
        //   //   Opcodes::CALL_GENERIC,
        //   //   AbstractMemorySize::new((func_inst.instantiation_size() + 1) as GasCarrier)
        //   // )?;
        //   let func = loader.function_at(func_inst.handle());
        //   let ty_args = func_inst.materialize(current_frame.ty_args())?;
        //   if func.is_native() {
        //     self.call_native(&resolver, context, func, ty_args)?;
        //     continue;
        //   }
        //   // TODO: when a native function is executed, the current frame has not yet
        //   // been pushed onto the call stack. Fix it.
        //   let frame = self
        //     .make_call_frame(solver, func, ty_args)
        //     .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
        //   self.call_stack.push(current_frame).or_else(|frame| {
        //     let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
        //     Err(self.maybe_core_dump(err, &frame))
        //   })?;
        //   current_frame = frame;
        // }
      }
    }
    solver.check(); //??? avoid unchecked get_model
    let model = solver.get_model();
    msg += "Test Function Arguments\n";
    for (i, v) in args.into_iter().enumerate() {
      msg += &format!("  {}: {:#?}\n", i, model.eval(&v.into_ast()?));
    }
    msg += "Test Function Returns\n";
    for i in 0..current_frame.function.return_count() {
      msg += &format!("  {}: {:#?}\n", i, self.operand_stack.pop()?);
    }
    msg += "-------------------------\n";
    print!("{}", msg);
    Ok(())
  }

  /// Returns a `SymFrame` if the call is to a Move function. Calls to native functions are
  /// "inlined" and this returns `None`.
  ///
  /// Native functions do not push a frame at the moment and as such errors from a native
  /// function are incorrectly attributed to the caller.
  fn make_call_frame(&mut self, context: &'ctx Context, func: Arc<Function>, ty_args: Vec<Type>) -> VMResult<SymFrame<'ctx>> {
    let mut locals = SymLocals::new(context, func.local_count());
    let arg_count = func.arg_count();
    for i in 0..arg_count {
      locals.store_loc(arg_count - i - 1, self.operand_stack.pop()?)?;
    }
    Ok(SymFrame::new(
      func,
      ty_args,
      locals
    ))
  }

  /// Call a native functions.
  // fn call_native(
  //   &mut self,
  //   resolver: &Resolver,
  //   context: &mut dyn SymbolicVMContext,
  //   function: Arc<Function>,
  //   ty_args: Vec<Type>,
  // ) -> VMResult<()> {
  //   let mut arguments = VecDeque::new();
  //   let expected_args = function.arg_count();
  //   for _ in 0..expected_args {
  //     arguments.push_front(self.operand_stack.pop()?);
  //   }
  //   let mut native_context = FunctionContext::new(self, context, resolver);
  //   let native_function = function.get_native()?;
  //   let result = native_function.dispatch(&mut native_context, ty_args, arguments)?;
  //   // gas!(consume: context, result.cost)?;
  //   result.result.and_then(|values| {
  //     for value in values {
  //       self.operand_stack.push(value)?;
  //     }
  //     Ok(())
  //   })
  // }

  /// Perform a binary operation to two values at the top of the stack.
  fn binop<F, T>(&mut self, f: F) -> VMResult<()>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> VMResult<SymValue<'ctx>>,
  {
    let rhs = self.operand_stack.pop_as::<T>()?;
    let lhs = self.operand_stack.pop_as::<T>()?;
    let result = f(lhs, rhs)?;
    self.operand_stack.push(result)
  }

  /// Perform a binary operation for integer values.
  fn binop_int<F>(&mut self, f: F) -> VMResult<()>
  where
    F: FnOnce(SymIntegerValue<'ctx>, SymIntegerValue<'ctx>) -> VMResult<SymIntegerValue<'ctx>>,
  {
    self.binop(|lhs, rhs| {
      Ok(match f(lhs, rhs)? {
        SymIntegerValue::U8(x) => SymValue::from_sym_u8(x),
        SymIntegerValue::U64(x) => SymValue::from_sym_u64(x),
        SymIntegerValue::U128(x) => SymValue::from_sym_u128(x),
      })
    })
  }

  /// Perform a binary operation for boolean values.
  fn binop_bool<F, T>(&mut self, f: F) -> VMResult<()>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> VMResult<SymBool<'ctx>>,
  {
    self.binop(|lhs, rhs| Ok(SymValue::from_sym_bool(f(lhs, rhs)?)))
  }

  /// Entry point for all global store operations (effectively opcodes).
  ///
  /// This performs common operation on the data store and then executes the specific
  /// opcode.
  fn global_data_op<F>(
    &mut self,
    resolver: &Resolver,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    address: AccountAddress,
    idx: StructDefinitionIndex,
    resource: Option<SymStruct<'ctx>>,
    op: F,
  ) -> VMResult<AbstractMemorySize<GasCarrier>>
  where
    F: FnOnce(
      &mut Self,
      &mut SymbolicVMContext<'vtxn, 'ctx>,
      AccessPath,
      &FatStructType,
      Option<SymStruct<'ctx>>,
    ) -> VMResult<AbstractMemorySize<GasCarrier>>,
  {
    let struct_type = resolver.struct_at(idx);
    let libra_type = resolver.get_libra_type_info(
      &struct_type.module,
      struct_type.name.as_ident_str(),
      &[],
      vm_ctx,
    )?;
    let ap = AccessPath::new(address, libra_type.resource_key().to_vec());
    op(self, vm_ctx, ap, libra_type.fat_type(), resource)
  }

  fn global_data_op_generic<F>(
    &mut self,
    resolver: &Resolver,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    address: AccountAddress,
    idx: StructDefInstantiationIndex,
    frame: &SymFrame,
    resource: Option<SymStruct<'ctx>>,
    op: F,
  ) -> VMResult<AbstractMemorySize<GasCarrier>>
  where
    F: FnOnce(
      &mut Self,
      &mut SymbolicVMContext<'vtxn, 'ctx>,
      AccessPath,
      &FatStructType,
      Option<SymStruct<'ctx>>,
    ) -> VMResult<AbstractMemorySize<GasCarrier>>,
  {
    let struct_inst = resolver.struct_instantiation_at(idx);
    let mut instantiation = vec![];
    for inst in struct_inst.get_instantiation() {
      instantiation.push(inst.subst(frame.ty_args())?);
    }
    let struct_type = resolver.struct_type_at(struct_inst.get_def_idx());
    let libra_type = resolver.get_libra_type_info(
      &struct_type.module,
      struct_type.name.as_ident_str(),
      &instantiation,
      vm_ctx,
    )?;
    let ap = AccessPath::new(address, libra_type.resource_key().to_vec());
    op(self, vm_ctx, ap, libra_type.fat_type(), resource)
  }

  /// BorrowGlobal (mutable and not) opcode.
  fn borrow_global(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    ap: AccessPath,
    struct_ty: &FatStructType,
    _resource: Option<SymStruct<'ctx>>,
  ) -> VMResult<AbstractMemorySize<GasCarrier>> {
    let g = self.state.borrow_global(vm_ctx, &ap, struct_ty)?;
    let size = g.size();
    self.operand_stack.push(g.borrow_global()?)?;
    Ok(size)
  }

  /// Exists opcode.
  fn exists(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    ap: AccessPath,
    struct_ty: &FatStructType,
    _resource: Option<SymStruct<'ctx>>,
  ) -> VMResult<AbstractMemorySize<GasCarrier>> {
    let (exists, mem_size) = self.state.resource_exists(vm_ctx, &ap, struct_ty)?;
    self.operand_stack.push(SymValue::from_bool(self.solver.get_context(), exists))?;
    Ok(mem_size)
  }

  /// MoveFrom opcode.
  fn move_from(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    ap: AccessPath,
    struct_ty: &FatStructType,
    _resource: Option<SymStruct<'ctx>>,
  ) -> VMResult<AbstractMemorySize<GasCarrier>> {
    let resource = self.state.move_resource_from(vm_ctx, &ap, struct_ty)?;
    let size = resource.size();
    self.operand_stack.push(resource)?;
    Ok(size)
  }

  /// MoveTo opcode.
  fn move_to(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    ap: AccessPath,
    struct_ty: &FatStructType,
    resource: Option<SymStruct<'ctx>>,
  ) -> VMResult<AbstractMemorySize<GasCarrier>> {
    match resource {
      Some(resource) => {
        let size = resource.size();
        self.state.move_resource_to(vm_ctx, &ap, struct_ty, resource)?;
        Ok(size)
      }
      None => Err(
        VMStatus::new(StatusCode::MOVETO_NO_RESOURCE_ERROR)
          .with_message("Should not happenned! SymInterpreter::move_to was not supplied with a resource!".to_string())
      )
    }
  }

  /// MoveToSender opcode.
  fn move_to_sender(
    &mut self,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    ap: AccessPath,
    struct_ty: &FatStructType,
    _resource: Option<SymStruct<'ctx>>,
  ) -> VMResult<AbstractMemorySize<GasCarrier>> {
    let resource = self.operand_stack.pop_as::<SymStruct>()?;
    let size = resource.size();
    self.state.move_resource_to(vm_ctx, &ap, struct_ty, resource)?;
    Ok(size)
  }

  //
  // Debugging and logging helpers.
  //

  /// Given an `VMStatus` generate a core dump if the error is an `InvariantViolation`.
  fn maybe_core_dump(&self, mut err: VMStatus, current_frame: &SymFrame) -> VMStatus {
    // a verification error cannot happen at runtime so change it into an invariant violation.
    if err.status_type() == StatusType::Verification {
      crit!("Verification error during runtime: {:?}", err);
      let mut new_err = VMStatus::new(StatusCode::VERIFICATION_ERROR);
      new_err.message = err.message;
      err = new_err;
    }
    if err.is(StatusType::InvariantViolation) {
      let state = self.get_internal_state(current_frame);
      crit!(
        "Error: {:?}\nCORE DUMP: >>>>>>>>>>>>\n{}\n<<<<<<<<<<<<\n",
        err,
        state,
      );
    }
    err
  }

  // #[allow(dead_code)]
  // fn debug_print_frame<B: Write>(
  //   &self,
  //   buf: &mut B,
  //   resolver: &Resolver,
  //   idx: usize,
  //   frame: &SymFrame,
  // ) -> VMResult<()> {
  //   // Print out the function name with type arguments.
  //   let func = &frame.function;

  //   debug_write!(buf, "    [{}] ", idx)?;
  //   if let Some(module) = func.module_id() {
  //     debug_write!(buf, "{}::{}::", module.address(), module.name(),)?;
  //   }
  //   debug_write!(buf, "{}", func.name())?;
  //   let ty_args = frame.ty_args();
  //   let mut fat_ty_args = vec![];
  //   for ty in ty_args {
  //     fat_ty_args.push(resolver.type_to_fat_type(ty)?);
  //   }
  //   if !fat_ty_args.is_empty() {
  //     debug_write!(buf, "<")?;
  //     let mut it = fat_ty_args.iter();
  //     if let Some(ty) = it.next() {
  //       ty.debug_print(buf)?;
  //       for ty in it {
  //         debug_write!(buf, ", ")?;
  //         ty.debug_print(buf)?;
  //       }
  //     }
  //     debug_write!(buf, ">")?;
  //   }
  //   debug_writeln!(buf)?;

  //   // Print out the current instruction.
  //   debug_writeln!(buf)?;
  //   debug_writeln!(buf, "        Code:")?;
  //   let pc = frame.pc as usize;
  //   let code = func.code();
  //   let before = if pc > 3 { pc - 3 } else { 0 };
  //   let after = min(code.len(), pc + 4);
  //   for (idx, instr) in code.iter().enumerate().take(pc).skip(before) {
  //     debug_writeln!(buf, "            [{}] {:?}", idx, instr)?;
  //   }
  //   debug_writeln!(buf, "          > [{}] {:?}", pc, &code[pc])?;
  //   for (idx, instr) in code.iter().enumerate().take(after).skip(pc + 1) {
  //     debug_writeln!(buf, "            [{}] {:?}", idx, instr)?;
  //   }

  //   // Print out the locals.
  //   debug_writeln!(buf)?;
  //   debug_writeln!(buf, "        SymLocals:")?;
  //   if func.local_count() > 0 {
  //     let mut tys = vec![];
  //     for local in &func.locals().0 {
  //       tys.push(resolver.make_fat_type(local, ty_args)?);
  //     }
  //     values::debug::print_locals(buf, &tys, &frame.locals)?;
  //     debug_writeln!(buf)?;
  //   } else {
  //     debug_writeln!(buf, "            (none)")?;
  //   }

  //   debug_writeln!(buf)?;
  //   Ok(())
  // }

  // #[allow(dead_code)]
  // pub(crate) fn debug_print_stack_trace<B: Write>(
  //   &self,
  //   buf: &mut B,
  //   resolver: &Resolver,
  // ) -> VMResult<()> {
  //   debug_writeln!(buf, "Call Stack:")?;
  //   for (i, frame) in self.call_stack.0.iter().enumerate() {
  //     self.debug_print_frame(buf, resolver, i, frame)?;
  //   }
  //   debug_writeln!(buf, "Operand Stack:")?;
  //   for (idx, val) in self.operand_stack.0.iter().enumerate() {
  //     // TODO: Currently we do not know the types of the values on the operand stack.
  //     // Revisit.
  //     debug_writeln!(buf, "    [{}] {}", idx, val)?;
  //   }
  //   Ok(())
  // }

  /// Generate a string which is the status of the interpreter: call stack, current bytecode
  /// stream, locals and operand stack.
  ///
  /// It is used when generating a core dump but can be used for debugging of the interpreter.
  /// It will be exposed via a debug module to give developers a way to print the internals
  /// of an execution.
  fn get_internal_state(&self, current_frame: &SymFrame) -> String {
    let mut internal_state = "Call stack:\n".to_string();
    for (i, frame) in self.call_stack.0.iter().enumerate() {
      internal_state.push_str(
        format!(
          " frame #{}: {} [pc = {}]\n",
          i,
          frame.function.pretty_string(),
          frame.pc,
        )
        .as_str(),
      );
    }
    internal_state.push_str(
      format!(
        "*frame #{}: {} [pc = {}]:\n",
        self.call_stack.0.len(),
        current_frame.function.pretty_string(),
        current_frame.pc,
      )
      .as_str(),
    );
    let code = current_frame.function.code();
    let pc = current_frame.pc as usize;
    if pc < code.len() {
      let mut i = 0;
      for bytecode in &code[..pc] {
        internal_state.push_str(format!("{}> {:?}\n", i, bytecode).as_str());
        i += 1;
      }
      internal_state.push_str(format!("{}* {:?}\n", i, code[pc]).as_str());
    }
    internal_state.push_str(format!("SymLocals:\n{}\n", current_frame.locals).as_str());
    internal_state.push_str("Operand Stack:\n");
    for value in &self.operand_stack.0 {
      internal_state.push_str(format!("{}\n", value).as_str());
    }
    internal_state
  }
}

pub enum SymInterpreterExecutionResult<'vtxn, 'ctx> {
  Fork(Vec<SymInterpreter<'vtxn, 'ctx>>),
  Report(Model<'ctx>, Vec<SymValue<'ctx>>)
}

// TODO Determine stack size limits based on gas limit
const OPERAND_STACK_SIZE_LIMIT: usize = 1024;
const CALL_STACK_SIZE_LIMIT: usize = 1024;

/// The operand stack.
pub struct SymStack<'ctx>(Vec<SymValue<'ctx>>); //??? should not be pub

impl<'ctx> SymStack<'ctx> {
  /// Create a new empty operand stack.
  fn new() -> Self {
    SymStack(vec![])
  }

  /// Push a `SymValue` on the stack if the max stack size has not been reached. Abort execution
  /// otherwise.
  pub fn push(&mut self, value: SymValue<'ctx>) -> VMResult<()> {
    if self.0.len() < OPERAND_STACK_SIZE_LIMIT {
      self.0.push(value);
      Ok(())
    } else {
      Err(VMStatus::new(StatusCode::EXECUTION_STACK_OVERFLOW))
    }
  }

  /// Pop a `SymValue` off the stack or abort execution if the stack is empty.
  pub fn pop(&mut self) -> VMResult<SymValue<'ctx>> {
    self
      .0
      .pop()
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))
  }

  /// Pop a `SymValue` of a given type off the stack. Abort if the value is not of the given
  /// type or if the stack is empty.
  pub fn pop_as<T>(&mut self) -> VMResult<T>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
  {
    self.pop()?.value_as()
  }

  /// Pop n values off the stack.
  pub fn popn(&mut self, n: u16) -> VMResult<Vec<SymValue<'ctx>>> {
    let remaining_stack_size = self
      .0
      .len()
      .checked_sub(n as usize)
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))?;
    let args = self.0.split_off(remaining_stack_size);
    Ok(args)
  }
}

impl<'ctx> Clone for SymStack<'ctx> {
  fn clone(&self) -> Self {
    SymStack(self.0.iter().map(|x| x.copy_value()).collect())
  }
} 

/// A call stack.
#[derive(Debug, Clone)]
struct SymCallStack<'ctx>(Vec<SymFrame<'ctx>>);

impl<'ctx> SymCallStack<'ctx> {
  /// Create a new empty call stack.
  fn new() -> Self {
    SymCallStack(vec![])
  }

  /// Push a `SymFrame` on the call stack.
  fn push(&mut self, frame: SymFrame<'ctx>) -> ::std::result::Result<(), SymFrame<'ctx>> {
    if self.0.len() < CALL_STACK_SIZE_LIMIT {
      self.0.push(frame);
      Ok(())
    } else {
      Err(frame)
    }
  }

  /// Pop a `SymFrame` off the call stack.
  fn pop(&mut self) -> Option<SymFrame<'ctx>> {
    self.0.pop()
  }
}

/// A `SymFrame` is the execution context for a function. It holds the locals of the function and
/// the function itself.
#[derive(Debug, Clone)]
struct SymFrame<'ctx> {
  pc: u16,
  locals: SymLocals<'ctx>,
  function: Arc<Function>,
  ty_args: Vec<Type>,
}

/// An `ExitCode` from `execute_code_unit`.
#[derive(Debug)]
enum ExitCode<'ctx> {
  Return,
  Call(FunctionHandleIndex),
  CallGeneric(FunctionInstantiationIndex),
  /// A `BrTrue / BrFalse` opcode was found.
  /// BrTrue / BrFalse, condition , offset
  Branch(bool, SymBool<'ctx>, CodeOffset),
}

impl<'ctx> SymFrame<'ctx> {
  /// Create a new `SymFrame` given a `Function` and the function `SymLocals`.
  ///
  /// The locals must be loaded before calling this.
  fn new(
    function: Arc<Function>,
    ty_args: Vec<Type>,
    locals: SymLocals<'ctx>
  ) -> Self {
    SymFrame {
      pc: 0,
      locals,
      function,
      ty_args,
    }
  }

  /// Execute a Move function until a return or a call opcode is found.
  fn execute_code<'vtxn>(
    &mut self,
    resolver: &Resolver,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    vm_ctx: &mut SymbolicVMContext<'vtxn, 'ctx>,
    manager: &mut PluginManager
  ) -> VMResult<ExitCode<'ctx>> {
    let code = self.function.code();
    loop {
      for instruction in &code[self.pc as usize..] {
        // trace!(self.function.pretty_string(), self.pc, instruction);
        self.pc += 1;

        manager.before_execute_instruction(interpreter, instruction)?;

        match instruction {
          Bytecode::Pop => {
            // gas!(const_instr: context, interpreter, Opcodes::POP)?;
            interpreter.operand_stack.pop()?;
          }
          Bytecode::Ret => {
            // gas!(const_instr: context, interpreter, Opcodes::RET)?;
            return Ok(ExitCode::Return);
          }
          Bytecode::BrTrue(offset) => {
            return Ok(ExitCode::Branch(true, interpreter.operand_stack.pop_as::<SymBool>()?, *offset));
            // gas!(const_instr: context, interpreter, Opcodes::BR_TRUE)?;
            // if interpreter.operand_stack.pop_as::<bool>()? {
            //   self.pc = *offset;
            //   break;
            // }
          }
          Bytecode::BrFalse(offset) => {
            return Ok(ExitCode::Branch(false, interpreter.operand_stack.pop_as::<SymBool>()?, *offset));
            // gas!(const_instr: context, interpreter, Opcodes::BR_FALSE)?;
            // if !interpreter.operand_stack.pop_as::<bool>()? {
            //   self.pc = *offset;
            //   break;
            // }
          }
          Bytecode::Branch(offset) => {
            // gas!(const_instr: context, interpreter, Opcodes::BRANCH)?;
            self.pc = *offset;
            break;
          }
          Bytecode::LdU8(int_const) => {
            // gas!(const_instr: context, interpreter, Opcodes::LD_U8)?;
            interpreter.operand_stack.push(SymValue::from_u8(interpreter.solver.get_context(), *int_const))?;
          }
          Bytecode::LdU64(int_const) => {
            // gas!(const_instr: context, interpreter, Opcodes::LD_U64)?;
            interpreter.operand_stack.push(SymValue::from_u64(interpreter.solver.get_context(), *int_const))?;
          }
          Bytecode::LdU128(int_const) => {
            // gas!(const_instr: context, interpreter, Opcodes::LD_U128)?;
            interpreter.operand_stack.push(SymValue::from_u128(interpreter.solver.get_context(), *int_const))?;
          }
          // !!!
          Bytecode::LdConst(idx) => {
            let constant = resolver.constant_at(*idx);
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::LD_CONST,
            //   AbstractMemorySize::new(constant.data.len() as GasCarrier)
            // )?;
            interpreter
              .operand_stack
              .push(SymValue::deserialize_constant(interpreter.solver.get_context(), constant).ok_or_else(|| {
                VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
                  "Verifier failed to verify the deserialization of constants".to_owned(),
                )
              })?)?
          }
          Bytecode::LdTrue => {
            // gas!(const_instr: context, interpreter, Opcodes::LD_TRUE)?;
            interpreter.operand_stack.push(SymValue::from_bool(interpreter.solver.get_context(), true))?;
          }
          Bytecode::LdFalse => {
            // gas!(const_instr: context, interpreter, Opcodes::LD_FALSE)?;
            interpreter.operand_stack.push(SymValue::from_bool(interpreter.solver.get_context(), false))?;
          }
          Bytecode::CopyLoc(idx) => {
            let local = self.locals.copy_loc(*idx as usize)?;
            // gas!(instr: context, interpreter, Opcodes::COPY_LOC, local.size())?;
            interpreter.operand_stack.push(local)?;
          }
          Bytecode::MoveLoc(idx) => {
            let local = self.locals.move_loc(*idx as usize)?;
            // gas!(instr: context, interpreter, Opcodes::MOVE_LOC, local.size())?;
            interpreter.operand_stack.push(local)?;
          }
          Bytecode::StLoc(idx) => {
            let value_to_store = interpreter.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::ST_LOC,
            //   value_to_store.size()
            // )?;
            self.locals.store_loc(*idx as usize, value_to_store)?;
          }
          Bytecode::Call(idx) => {
            return Ok(ExitCode::Call(*idx));
          }
          Bytecode::CallGeneric(idx) => {
            return Ok(ExitCode::CallGeneric(*idx));
          }
          Bytecode::MutBorrowLoc(idx) | Bytecode::ImmBorrowLoc(idx) => {
            // let opcode = match instruction {
            //   Bytecode::MutBorrowLoc(_) => Opcodes::MUT_BORROW_LOC,
            //   _ => Opcodes::IMM_BORROW_LOC,
            // };
            // gas!(const_instr: context, interpreter, opcode)?;
            interpreter
              .operand_stack
              .push(self.locals.borrow_loc(*idx as usize)?)?;
          }
          Bytecode::ImmBorrowField(fh_idx) | Bytecode::MutBorrowField(fh_idx) => {
            // let opcode = match instruction {
            //   Bytecode::MutBorrowField(_) => Opcodes::MUT_BORROW_FIELD,
            //   _ => Opcodes::IMM_BORROW_FIELD,
            // };
            // gas!(const_instr: context, interpreter, opcode)?;

            let reference = interpreter.operand_stack.pop_as::<SymStructRef>()?;
            let offset = resolver.field_offset(*fh_idx);
            let field_ref = reference.borrow_field(offset)?;
            interpreter.operand_stack.push(field_ref)?;
          }
          Bytecode::ImmBorrowFieldGeneric(fi_idx) | Bytecode::MutBorrowFieldGeneric(fi_idx) => {
            // let opcode = match instruction {
            //   Bytecode::MutBorrowField(_) => Opcodes::MUT_BORROW_FIELD_GENERIC,
            //   _ => Opcodes::IMM_BORROW_FIELD_GENERIC,
            // };
            // gas!(const_instr: context, interpreter, opcode)?;

            let reference = interpreter.operand_stack.pop_as::<SymStructRef>()?;
            let offset = resolver.field_instantiation_offset(*fi_idx);
            let field_ref = reference.borrow_field(offset)?;
            interpreter.operand_stack.push(field_ref)?;
          }
          Bytecode::Pack(sd_idx) => {
            let field_count = resolver.field_count(*sd_idx);
            let args = interpreter.operand_stack.popn(field_count)?;
            // let size = args.iter().fold(
            //   AbstractMemorySize::new(GasCarrier::from(field_count)),
            //   |acc, v| acc.add(v.size()),
            // );
            // gas!(instr: context, interpreter, Opcodes::PACK, size)?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_struct(SymStruct::pack(interpreter.solver.get_context(), args)))?;
          }
          Bytecode::PackGeneric(si_idx) => {
            let field_count = resolver.field_instantiation_count(*si_idx);
            let args = interpreter.operand_stack.popn(field_count)?;
            // let size = args.iter().fold(
            //   AbstractMemorySize::new(GasCarrier::from(field_count)),
            //   |acc, v| acc.add(v.size()),
            // );
            // gas!(instr: context, interpreter, Opcodes::PACK, size)?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_struct(SymStruct::pack(interpreter.solver.get_context(), args)))?;
          }
          Bytecode::Unpack(_sd_idx) => {
            // let field_count = resolver.field_count(*sd_idx);
            let struct_ = interpreter.operand_stack.pop_as::<SymStruct>()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::UNPACK,
            //   AbstractMemorySize::new(GasCarrier::from(field_count))
            // )?;
            // TODO: Whether or not we want this gas metering in the loop is
            // questionable.  However, if we don't have it in the loop we could wind up
            // doing a fair bit of work before charging for it.
            for value in struct_.unpack()? {
              // gas!(instr: context, interpreter, Opcodes::UNPACK, value.size())?;
              interpreter.operand_stack.push(value)?;
            }
          }
          Bytecode::UnpackGeneric(_si_idx) => {
            // let field_count = resolver.field_instantiation_count(*si_idx);
            let struct_ = interpreter.operand_stack.pop_as::<SymStruct>()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::UNPACK_GENERIC,
            //   AbstractMemorySize::new(GasCarrier::from(field_count))
            // )?;
            // TODO: Whether or not we want this gas metering in the loop is
            // questionable.  However, if we don't have it in the loop we could wind up
            // doing a fair bit of work before charging for it.
            for value in struct_.unpack()? {
              // gas!(
              //   instr: context,
              //   interpreter,
              //   Opcodes::UNPACK_GENERIC,
              //   value.size()
              // )?;
              interpreter.operand_stack.push(value)?;
            }
          }
          Bytecode::ReadRef => {
            let reference = interpreter.operand_stack.pop_as::<SymReference>()?;
            let value = reference.read_ref()?;
            // gas!(instr: context, interpreter, Opcodes::READ_REF, value.size())?;
            interpreter.operand_stack.push(value)?;
          }
          Bytecode::WriteRef => {
            let reference = interpreter.operand_stack.pop_as::<SymReference>()?;
            let value = interpreter.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::WRITE_REF,
            //   value.size()
            // )?;
            reference.write_ref(value)?;
          }
          Bytecode::CastU8 => {
            // gas!(const_instr: context, interpreter, Opcodes::CAST_U8)?;
            let integer_value = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_u8(integer_value.cast_u8()))?;
          }
          Bytecode::CastU64 => {
            // gas!(const_instr: context, interpreter, Opcodes::CAST_U64)?;
            let integer_value = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_u64(integer_value.cast_u64()))?;
          }
          Bytecode::CastU128 => {
            // gas!(const_instr: context, interpreter, Opcodes::CAST_U128)?;
            let integer_value = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_u128(integer_value.cast_u128()))?;
          }
          // Arithmetic Operations
          Bytecode::Add => {
            // gas!(const_instr: context, interpreter, Opcodes::ADD)?;
            interpreter.binop_int(SymIntegerValue::add)?
          }
          Bytecode::Sub => {
            // gas!(const_instr: context, interpreter, Opcodes::SUB)?;
            interpreter.binop_int(SymIntegerValue::sub)?
          }
          Bytecode::Mul => {
            // gas!(const_instr: context, interpreter, Opcodes::MUL)?;
            interpreter.binop_int(SymIntegerValue::mul)?
          }
          Bytecode::Mod => {
            // gas!(const_instr: context, interpreter, Opcodes::MOD)?;
            interpreter.binop_int(SymIntegerValue::rem)?
          }
          Bytecode::Div => {
            // gas!(const_instr: context, interpreter, Opcodes::DIV)?;
            interpreter.binop_int(SymIntegerValue::div)?
          }
          Bytecode::BitOr => {
            // gas!(const_instr: context, interpreter, Opcodes::BIT_OR)?;
            interpreter.binop_int(SymIntegerValue::bit_or)?
          }
          Bytecode::BitAnd => {
            // gas!(const_instr: context, interpreter, Opcodes::BIT_AND)?;
            interpreter.binop_int(SymIntegerValue::bit_and)?
          }
          Bytecode::Xor => {
            // gas!(const_instr: context, interpreter, Opcodes::XOR)?;
            interpreter.binop_int(SymIntegerValue::bit_xor)?
          }
          Bytecode::Shl => {
            // gas!(const_instr: context, interpreter, Opcodes::SHL)?;
            let rhs = interpreter.operand_stack.pop_as::<SymU8>()?;
            let lhs = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
            interpreter
              .operand_stack
              .push(lhs.shl(rhs)?.into_value())?;
          }
          Bytecode::Shr => {
            // gas!(const_instr: context, interpreter, Opcodes::SHR)?;
            let rhs = interpreter.operand_stack.pop_as::<SymU8>()?;
            let lhs = interpreter.operand_stack.pop_as::<SymIntegerValue>()?;
            interpreter
              .operand_stack
              .push(lhs.shr(rhs)?.into_value())?;
          }
          Bytecode::Or => {
            // gas!(const_instr: context, interpreter, Opcodes::OR)?;
            interpreter.binop_bool(|l: SymBool<'ctx>, r| Ok(l.or(&r)))?
          }
          Bytecode::And => {
            // gas!(const_instr: context, interpreter, Opcodes::AND)?;
            interpreter.binop_bool(|l: SymBool<'ctx>, r| Ok(l.and(&r)))?
          }
          Bytecode::Lt => {
            // gas!(const_instr: context, interpreter, Opcodes::LT)?;
            interpreter.binop_bool(SymIntegerValue::lt)?
          }
          Bytecode::Gt => {
            // gas!(const_instr: context, interpreter, Opcodes::GT)?;
            interpreter.binop_bool(SymIntegerValue::gt)?
          }
          Bytecode::Le => {
            // gas!(const_instr: context, interpreter, Opcodes::LE)?;
            interpreter.binop_bool(SymIntegerValue::le)?
          }
          Bytecode::Ge => {
            // gas!(const_instr: context, interpreter, Opcodes::GE)?;
            interpreter.binop_bool(SymIntegerValue::ge)?
          }
          Bytecode::Abort => {
            // gas!(const_instr: context, interpreter, Opcodes::ABORT)?;
            let sym_error_code = interpreter.operand_stack.pop_as::<SymU64>()?;
            let error_code = sym_error_code.as_inner().as_u64();
            return match error_code {
              Some(code) => Err(
                VMStatus::new(StatusCode::ABORTED)
                  .with_sub_status(code)
                  .with_message(format!(
                    "{} at offset {}",
                    self.function.pretty_string(),
                    self.pc,
                  )),
              ),
              None => {
                let msg = format!(
                  "With Symbolic Error Code {:?}, {} at offset {}",
                  error_code,
                  self.function.pretty_string(),
                  self.pc,
                );
                Err(VMStatus::new(StatusCode::ABORTED).with_message(msg))
              }
            };
          }
          Bytecode::Eq => {
            let lhs = interpreter.operand_stack.pop()?;
            let rhs = interpreter.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::EQ,
            //   lhs.size().add(rhs.size())
            // )?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_bool(lhs.equals(&rhs)?))?;
          }
          Bytecode::Neq => {
            let lhs = interpreter.operand_stack.pop()?;
            let rhs = interpreter.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::NEQ,
            //   lhs.size().add(rhs.size())
            // )?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_bool(lhs.equals(&rhs)?.not()))?;
          }
          Bytecode::GetTxnSenderAddress => {
            // gas!(const_instr: context, interpreter, Opcodes::GET_TXN_SENDER)?;
            interpreter
              .operand_stack
              .push(SymValue::from_address(interpreter.solver.get_context(), interpreter.txn_data.sender()))?;
          }
          Bytecode::MutBorrowGlobal(sd_idx) | Bytecode::ImmBorrowGlobal(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op(
              resolver,
              vm_ctx,
              addr,
              *sd_idx,
              None,
              SymInterpreter::borrow_global,
            )?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MUT_BORROW_GLOBAL,
            //   size
            // )?;
          }
          Bytecode::MutBorrowGlobalGeneric(si_idx) | Bytecode::ImmBorrowGlobalGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op_generic(
              resolver,
              vm_ctx,
              addr,
              *si_idx,
              self,
              None,
              SymInterpreter::borrow_global,
            )?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MUT_BORROW_GLOBAL_GENERIC,
            //   size
            // )?;
          }
          Bytecode::Exists(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size =
              interpreter.global_data_op(resolver, vm_ctx, addr, *sd_idx, None, SymInterpreter::exists)?;
            // gas!(instr: context, interpreter, Opcodes::EXISTS, size)?;
          }
          Bytecode::ExistsGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op_generic(
              resolver,
              vm_ctx,
              addr,
              *si_idx,
              self,
              None,
              SymInterpreter::exists,
            )?;
            // gas!(instr: context, interpreter, Opcodes::EXISTS_GENERIC, size)?;
          }
          Bytecode::MoveFrom(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op(
              resolver,
              vm_ctx,
              addr,
              *sd_idx,
              None,
              SymInterpreter::move_from,
            )?;
            // TODO: Have this calculate before pulling in the data based upon
            // the size of the data that we are about to read in.
            // gas!(instr: context, interpreter, Opcodes::MOVE_FROM, size)?;
          }
          Bytecode::MoveFromGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op_generic(
              resolver,
              vm_ctx,
              addr,
              *si_idx,
              self,
              None,
              SymInterpreter::move_from,
            )?;
            // TODO: Have this calculate before pulling in the data based upon
            // the size of the data that we are about to read in.
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MOVE_FROM_GENERIC,
            //   size
            // )?;
          }
          Bytecode::MoveToSender(sd_idx) => {
            let addr = interpreter.txn_data.sender();
            let _size = interpreter.global_data_op(
              resolver,
              vm_ctx,
              addr,
              *sd_idx,
              None,
              SymInterpreter::move_to_sender,
            )?;
            // gas!(instr: context, interpreter, Opcodes::MOVE_TO_SENDER, size)?;
          }
          Bytecode::MoveToSenderGeneric(si_idx) => {
            let addr = interpreter.txn_data.sender();
            let _size = interpreter.global_data_op_generic(
              resolver,
              vm_ctx,
              addr,
              *si_idx,
              self,
              None,
              SymInterpreter::move_to_sender,
            )?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MOVE_TO_SENDER_GENERIC,
            //   size
            // )?;
          }
          Bytecode::MoveTo(sd_idx) => {
            let resource = interpreter.operand_stack.pop_as::<SymStruct>()?;
            let signer_reference = interpreter.operand_stack.pop_as::<SymReference>()?;
            let addr = signer_reference.read_ref()?.value_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op(
              resolver,
              vm_ctx,
              addr,
              *sd_idx,
              Some(resource),
              SymInterpreter::move_to,
            )?;
            // gas!(instr: context, interpreter, Opcodes::MOVE_TO, size)?;
          }
          Bytecode::MoveToGeneric(si_idx) => {
            let resource = interpreter.operand_stack.pop_as::<SymStruct>()?;
            let signer_reference = interpreter.operand_stack.pop_as::<SymReference>()?;
            let addr = signer_reference.read_ref()?.value_as::<SymAccountAddress>()?.into_address();
            let _size = interpreter.global_data_op_generic(
              resolver,
              vm_ctx,
              addr,
              *si_idx,
              self,
              Some(resource),
              SymInterpreter::move_to,
            )?;
            // gas!(instr: context, interpreter, Opcodes::MOVE_TO_GENERIC, size)?;
          }
          Bytecode::FreezeRef => {
            // FreezeRef should just be a null op as we don't distinguish between mut
            // and immut ref at runtime.
          }
          Bytecode::Not => {
            // gas!(const_instr: context, interpreter, Opcodes::NOT)?;
            let value = interpreter.operand_stack.pop_as::<SymBool>()?.not();
            interpreter.operand_stack.push(SymValue::from_sym_bool(value))?;
          }
          Bytecode::Nop => {
            // gas!(const_instr: context, interpreter, Opcodes::NOP)?;
          }
        }
      }
      // ok we are out, it's a branch, check the pc for good luck
      // TODO: re-work the logic here. Tests should have a more
      // natural way to plug in
      if self.pc as usize >= code.len() {
        if cfg!(test) {
          // In order to test the behavior of an instruction stream, hitting end of the
          // code should report no error so that we can check the
          // locals.
          return Ok(ExitCode::Return);
        } else {
          return Err(VMStatus::new(StatusCode::PC_OVERFLOW));
        }
      }
    }
  }

  fn ty_args(&self) -> &[Type] {
    &self.ty_args
  }

  fn resolver<'a>(&self, loader: &'a Loader) -> Resolver<'a> {
    self.function.get_resolver(loader)
  }
}
