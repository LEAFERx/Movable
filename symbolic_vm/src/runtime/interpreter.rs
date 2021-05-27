// use move_vm_runtime::{
//   gas,
//   loader::{Function, Loader, Resolver},
//   native_functions::FunctionContext,
//   trace,
// };
use diem_types::account_address::AccountAddress;
use move_core_types::{
  gas_schedule::{AbstractMemorySize, /* CostTable, GasAlgebra, */ GasCarrier},
  vm_status::{StatusCode, StatusType},
};
use move_vm_types::{
  loaded_data::runtime_types::Type,
};
use move_vm_runtime::data_cache::RemoteCache;
use crate::{
  plugin::{
    PluginManager,
    PluginContext,
  },
  runtime::{
    data_cache::SymDataCache,
    loader::{Function, Loader, Resolver},
    native_functions::SymFunctionContext,
  },
  types::{
    data_store::SymDataStore,
    values::{
      SymU8, SymU64, SymBool, SymAccountAddress, SymIntegerValue,
      SymLocals, SymReference, SymStruct, SymStructRef, SymValue, VMSymValueCast,
      SymGlobalValue,
    },
  },
};

use std::{
  collections::VecDeque,
  sync::Arc,
};
use vm::{
  errors::*,
  file_format::{
    Bytecode, CodeOffset, FunctionHandleIndex, FunctionInstantiationIndex,
  },
};

use z3::{Context, Solver, SatResult, Model};

// macro_rules! debug_write {
//   ($($toks: tt)*) => {
//       write!($($toks)*).map_err(|_|
//           PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//               .with_message("failed to write to buffer".to_string())
//       )
//   };
// }

// macro_rules! debug_writeln {
//   ($($toks: tt)*) => {
//       writeln!($($toks)*).map_err(|_|
//           PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
//               .with_message("failed to write to buffer".to_string())
//       )
//   };
// }

macro_rules! set_err_info {
  ($frame:ident, $e:expr) => {{
      $e.at_code_offset($frame.function.index(), $frame.pc)
          .finish($frame.location())
  }};
}

/// `Interpreter` instances can execute Move functions.
///
/// An `Interpreter` instance is a stand alone execution context for a function.
/// It mimics execution on a single thread, with an call stack and an operand stack.

// TODO: for convenient currently the struct and fields are made public, fix it
pub struct SymInterpreter<'ctx, 'r, 'l, R> {
  /// Operand stack, where Move `SymValue`s are stored for stack operations.
  pub operand_stack: SymStack<'ctx>,
  /// The stack of active functions.
  call_stack: SymCallStack<'ctx>,
  // gas_schedule: &'vtxn CostTable,
  /// Z3 solver
  pub solver: Solver<'ctx>,
  pub path_conditions: Vec<SymBool<'ctx>>,
  pub spec_conditions: Vec<(Vec<SymValue<'ctx>>, SymBool<'ctx>)>,
  pub data_cache: SymDataCache<'ctx, 'r, 'l, R>, 
}

impl<'ctx, 'r, 'l, R: RemoteCache> SymInterpreter<'ctx, 'r, 'l, R> {
  /// Entrypoint into the interpreter. All external calls need to be routed through this
  /// function.
  pub(crate) fn entrypoint(
    z3_ctx: &'ctx Context,
    function: Arc<Function>,
    ty_args: Vec<Type>,
    args: Vec<SymValue<'ctx>>,
    data_cache: SymDataCache<'ctx, 'r, 'l, R>,
    // cost_strategy: &mut 
    loader: &'l Loader,
  ) -> VMResult<Self> {
    let mut interp = Self::new(z3_ctx, data_cache);
    
    let mut locals = SymLocals::new(z3_ctx, function.local_count());
    // TODO: assert consistency of args and function formals
    for (i, value) in args.into_iter().enumerate() {
      // TODO: wrong error handling...
      locals.store_loc(i, value).map_err(|err| err.finish(Location::Undefined))?;
    }
    let current_frame = SymFrame::new(z3_ctx, function, ty_args, locals);
    interp.call_stack.push(current_frame).map_err(|frame| {
      let err = PartialVMError::new(StatusCode::CALL_STACK_OVERFLOW);
      let err = set_err_info!(frame, err);
      interp.maybe_core_dump(err, &frame)
    })?;
    Ok(interp)
  }

  /// Create a new instance of an `Interpreter` in the context of a transaction with a
  /// given module cache and gas schedule.
  fn new(
    z3_ctx: &'ctx Context,
    // cost_strategy: &mut 
    data_cache: SymDataCache<'ctx, 'r, 'l, R>,
  ) -> Self {
    SymInterpreter {
      operand_stack: SymStack::new(),
      call_stack: SymCallStack::new(),
      solver: Solver::new(&z3_ctx),
      path_conditions: vec![],
      spec_conditions: vec![],
      data_cache,
    }
  }

  fn fork(&self) -> Self {
    SymInterpreter {
      operand_stack: self.operand_stack.fork(),
      call_stack: self.call_stack.fork(),
      solver: self.solver.translate(self.solver.get_context()),
      path_conditions: self.path_conditions.clone(),
      spec_conditions: self.spec_conditions.iter().map(
        |(args, cond)| (args.iter().map(|v| v.copy_value().unwrap()).collect(), cond.clone())
      ).collect(),
      data_cache: self.data_cache.fork(),
    }
  }

  pub(crate) fn data_cache(&mut self) -> &mut SymDataCache<'ctx, 'r, 'l, R> {
    &mut self.data_cache
  }

  // pub(crate) fn gas_schedule(&self) -> &CostTable {
  //   self.gas_schedule
  // }

  /// Continue to execute
  pub(crate) fn execute(
    mut self,
    loader: &'l Loader,
    manager: &mut PluginManager<'_, 'ctx>,
  ) -> VMResult<SymInterpreterExecutionResult<'ctx, 'r, 'l, R>> {
    if let Some(mut current_frame) = self.call_stack.pop() {
      loop {
        let resolver = current_frame.resolver(loader);
        let exit_code = current_frame
          .execute_code(&resolver, &mut self, manager)
          .map_err(|err| self.maybe_core_dump(err, &current_frame))?;
        match exit_code {
          ExitCode::Return => {
            if let Some(frame) = self.call_stack.pop() {
              current_frame = frame;
              current_frame.pc += 1;
            } else {
              // Ok we have touched the end of the path, now let's report
              println!("Path explored: {:?}", self.solver);
              let mut return_values = vec![];
              for _ in 0..current_frame.function.return_count() {
                let val = self.operand_stack
                  .pop()
                  .map_err(|e| set_err_info!(current_frame, e))?;
                return_values.push(val);
              }
              manager.after_execute(&mut self, return_values.as_slice())?;
              self.solver.check(); // TODO: avoid unchecked get_model
              return Ok(SymInterpreterExecutionResult::Report(
                self.solver.get_model().expect("No Model Avaliable"), return_values));
            }
          }
          ExitCode::Call(fh_idx) => {
            let func = resolver.function_from_handle(fh_idx);
            let should_skip = manager
              .before_call(&mut self, func.as_ref(), vec![])
              .map_err(|e| set_err_info!(current_frame, e))?;
            if should_skip {
              current_frame.pc += 1;
              continue;
            }
            if func.is_native() {
              self.call_native(&resolver, func, vec![])?;
              current_frame.pc += 1;
              continue;
            }
            let frame = self
              .make_call_frame(self.solver.get_context(), func, vec![])
              .map_err(|err| self.maybe_core_dump(err, &current_frame))?;
            self.call_stack.push(current_frame).map_err(|frame| {
              let err = PartialVMError::new(StatusCode::CALL_STACK_OVERFLOW);
              let err = set_err_info!(frame, err);
              self.maybe_core_dump(err, &frame)
            })?;
            current_frame = frame;
          }
          ExitCode::CallGeneric(idx) => {
            let arity = resolver.type_params_count(idx);
            let ty_args = resolver
              .instantiate_generic_function(idx, current_frame.ty_args())
              .map_err(|e| set_err_info!(current_frame, e))?;
            let func = resolver.function_from_instantiation(idx);
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::CALL_GENERIC,
            //   AbstractMemorySize::new((func_inst.instantiation_size() + 1) as GasCarrier)
            // )?;
            let should_skip = manager
              .before_call(&mut self, func.as_ref(), ty_args.clone())
              .map_err(|e| set_err_info!(current_frame, e))?;
            if should_skip {
              current_frame.pc += 1;
              continue;
            }
            if func.is_native() {
              self.call_native(&resolver, func, ty_args)?;
              current_frame.pc += 1;
              continue;
            }
            let frame = self
              .make_call_frame(self.solver.get_context(), func, vec![])
              .map_err(|err| self.maybe_core_dump(err, &current_frame))?;
            self.call_stack.push(current_frame).map_err(|frame| {
              let err = PartialVMError::new(StatusCode::CALL_STACK_OVERFLOW);
              let err = set_err_info!(frame, err);
              self.maybe_core_dump(err, &frame)
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
            let mut forked_frame = current_frame.fork();

            if instr {
              current_frame.pc = offset;
              forked_frame.pc += 1;
            } else {
              forked_frame.pc = offset;
              current_frame.pc += 1;
            }

            self.call_stack.push(current_frame).map_err(|frame| {
              let err = PartialVMError::new(StatusCode::CALL_STACK_OVERFLOW);
              let err = set_err_info!(frame, err);
              self.maybe_core_dump(err, &frame)
            })?;

            forked_interp.call_stack.push(forked_frame).map_err(|frame| {
              let err = PartialVMError::new(StatusCode::CALL_STACK_OVERFLOW);
              let err = set_err_info!(frame, err);
              self.maybe_core_dump(err, &frame)
            })?;

            self.solver.assert(&condition.as_inner());
            if self.solver.check() == SatResult::Sat {
              self.path_conditions.push(condition.clone());
              forks.push(self);
            }
            
            let neg_condition_ast = condition.as_inner().not();
            forked_interp.solver.assert(&neg_condition_ast);
            let neg_condition = SymBool::from_ast(neg_condition_ast);
            if forked_interp.solver.check() == SatResult::Sat {
              forked_interp.path_conditions.push(neg_condition);
              forks.push(forked_interp);
            }
            return Ok(SymInterpreterExecutionResult::Fork(forks));
          }
        }
      }
    } else {
      Err(
        PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("Execute on empty call stack!".to_string())
          .finish(Location::Undefined)
      )
    }
  }

  /// Returns a `SymFrame` if the call is to a Move function. Calls to native functions are
  /// "inlined" and this returns `None`.
  ///
  /// Native functions do not push a frame at the moment and as such errors from a native
  /// function are incorrectly attributed to the caller.
  fn make_call_frame(&mut self, z3_ctx: &'ctx Context, func: Arc<Function>, ty_args: Vec<Type>) -> VMResult<SymFrame<'ctx>> {
    let mut locals = SymLocals::new(z3_ctx, func.local_count());
    let arg_count = func.arg_count();
    for i in 0..arg_count {
      locals
        .store_loc(
          arg_count - i - 1,
          self.operand_stack.pop().map_err(|e| self.set_location(e))?
        )
        .map_err(|e| self.set_location(e))?;
    }
    Ok(SymFrame::new(
      z3_ctx,
      func,
      ty_args,
      locals
    ))
  }

  /// Call a native functions.
  fn call_native(
    &mut self,
    resolver: &Resolver<'l>,
    function: Arc<Function>,
    ty_args: Vec<Type>,
  ) -> VMResult<()> {
    self.call_native_impl(resolver, function.clone(), ty_args)
      .map_err(|e| match function.module_id() {
        Some(id) => e
          .at_code_offset(function.index(), 0)
          .finish(Location::Module(id.clone())),
        None => {
          let err = PartialVMError::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
            .with_message("Unexpected native function not located in a module".to_owned());
          self.set_location(err)
        }
      })
  }

  fn call_native_impl(
    &mut self,
    resolver: &Resolver<'l>,
    function: Arc<Function>,
    ty_args: Vec<Type>,
  ) -> PartialVMResult<()> {
    let mut arguments = VecDeque::new();
    let expected_args = function.arg_count();
    for _ in 0..expected_args {
      arguments.push_front(self.operand_stack.pop()?);
    }
    let mut native_context = SymFunctionContext::new(self, resolver);
    let native_function = function.get_native()?;
    let result = native_function.dispatch(&mut native_context, ty_args, arguments)?;
    let return_values = result
      .result
      .map_err(|code| PartialVMError::new(StatusCode::ABORTED).with_sub_status(code))?;
    for value in return_values {
      self.operand_stack.push(value)?;
    }
    Ok(())
  }

  /// Perform a binary operation to two values at the top of the stack.
  fn binop<F, T>(&mut self, f: F) -> PartialVMResult<()>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> PartialVMResult<SymValue<'ctx>>,
  {
    let rhs = self.operand_stack.pop_as::<T>()?;
    let lhs = self.operand_stack.pop_as::<T>()?;
    let result = f(lhs, rhs)?;
    self.operand_stack.push(result)
  }

  /// Perform a binary operation for integer values.
  fn binop_int<F>(&mut self, f: F) -> PartialVMResult<()>
  where
    F: FnOnce(SymIntegerValue<'ctx>, SymIntegerValue<'ctx>) -> PartialVMResult<SymIntegerValue<'ctx>>,
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
  fn binop_bool<F, T>(&mut self, f: F) -> PartialVMResult<()>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> PartialVMResult<SymBool<'ctx>>,
  {
    self.binop(|lhs, rhs| Ok(SymValue::from_sym_bool(f(lhs, rhs)?)))
  }

  /// Load a resource from the data store.
  fn load_resource(
    &mut self,
    addr: AccountAddress,
    ty: &Type,
  ) -> PartialVMResult<&mut SymGlobalValue<'ctx>> {
    match self.data_cache.load_resource(addr, ty) {
      Ok(gv) => Ok(gv),
      Err(e) => {
        // log_context.alert();
        // error!(
        //   *log_context,
        //   "[VM] error loading resource at ({}, {:?}): {:?} from data store", addr, ty, e
        // );
        Err(e)
      }
    }
  }

  /// BorrowGlobal (mutable and not) opcode.
  fn borrow_global(
    &mut self,
    addr: AccountAddress,
    ty: &Type,
  ) -> PartialVMResult<AbstractMemorySize<GasCarrier>> {
    let g = self.load_resource(addr, ty)?.borrow_global()?;
    let size = g.size();
    self.operand_stack.push(g)?;
    Ok(size)
  }

  /// Exists opcode.
  fn exists(
    &mut self,
    addr: AccountAddress,
    ty: &Type,
  ) -> PartialVMResult<AbstractMemorySize<GasCarrier>> {
    let gv = self.load_resource(addr, ty)?;
    let mem_size = gv.size();
    let exists = gv.exists()?;
    self.operand_stack.push(SymValue::from_bool(
      self.solver.get_context(), exists))?;
    Ok(mem_size)
  }

  /// MoveFrom opcode.
  fn move_from(
    &mut self,
    addr: AccountAddress,
    ty: &Type,
  ) -> PartialVMResult<AbstractMemorySize<GasCarrier>> {
    let resource = self.load_resource(addr, ty)?.move_from()?;
    let size = resource.size();
    self.operand_stack.push(resource)?;
    Ok(size)
  }

  /// MoveTo opcode.
  fn move_to(
    &mut self,
    addr: AccountAddress,
    ty: &Type,
    resource: SymValue<'ctx>,
  ) -> PartialVMResult<AbstractMemorySize<GasCarrier>> {
    let size = resource.size();
    self.load_resource(addr, ty)?.move_to(resource)?;
    Ok(size)
  }

  //
  // Debugging and logging helpers.
  //

  /// Given an `VMStatus` generate a core dump if the error is an `InvariantViolation`.
  fn maybe_core_dump(&self, mut err: VMError, current_frame: &SymFrame<'ctx>) -> VMError {
    // a verification error cannot happen at runtime so change it into an invariant violation.
    if err.status_type() == StatusType::Verification {
      // self.log_context.alert();
      // error!(
      //   self.log_context,
      //   "Verification error during runtime: {:?}", err
      // );
      let new_err = PartialVMError::new(StatusCode::VERIFICATION_ERROR);
      let new_err = match err.message() {
          None => new_err,
          Some(msg) => new_err.with_message(msg.to_owned()),
      };
      err = new_err.finish(err.location().clone())
    }
    if err.status_type() == StatusType::InvariantViolation {
      let state = self.get_internal_state(current_frame);
      // self.log_context.alert();
      // error!(
      //   self.log_context,
      //   "Error: {:?}\nCORE DUMP: >>>>>>>>>>>>\n{}\n<<<<<<<<<<<<\n", err, state,
      // );
    }
    err
  }

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

  fn set_location(&self, err: PartialVMError) -> VMError {
    err.finish(self.call_stack.current_location())
  }
}

impl<'ctx, 'r, 'l, R: RemoteCache> PluginContext<'ctx> for SymInterpreter<'ctx, 'r, 'l, R> {
  fn z3_ctx(&self) -> &'ctx Context {
    self.data_cache.get_z3_ctx()
  }

  fn solver(&self) -> &Solver<'ctx> {
    &self.solver
  }

  fn operand_stack(&self) -> &SymStack<'ctx> {
    &self.operand_stack
  }

  fn path_conditions(&self) -> &Vec<SymBool<'ctx>> {
    &self.path_conditions
  }

  fn spec_conditions(&self) -> &Vec<(Vec<SymValue<'ctx>>, SymBool<'ctx>)> {
    &self.spec_conditions
  }

  fn operand_stack_mut(&mut self) -> &mut SymStack<'ctx> {
    &mut self.operand_stack
  }

  fn path_conditions_mut(&mut self) -> &mut Vec<SymBool<'ctx>> {
    &mut self.path_conditions
  }

  fn spec_conditions_mut(&mut self) -> &mut Vec<(Vec<SymValue<'ctx>>, SymBool<'ctx>)> {
    &mut self.spec_conditions
  }
}

pub enum SymInterpreterExecutionResult<'ctx, 'r, 'l, R> {
  Fork(Vec<SymInterpreter<'ctx, 'r, 'l, R>>),
  Report(Model<'ctx>, Vec<SymValue<'ctx>>)
}

// TODO Determine stack size limits based on gas limit
const OPERAND_STACK_SIZE_LIMIT: usize = 1024;
const CALL_STACK_SIZE_LIMIT: usize = 1024;

/// The operand stack.
pub struct SymStack<'ctx>(Vec<SymValue<'ctx>>); // TODO: should not be pub

impl<'ctx> SymStack<'ctx> {
  /// Create a new empty operand stack.
  fn new() -> Self {
    SymStack(vec![])
  }

  /// Push a `SymValue` on the stack if the max stack size has not been reached. Abort execution
  /// otherwise.
  pub fn push(&mut self, value: SymValue<'ctx>) -> PartialVMResult<()> {
    if self.0.len() < OPERAND_STACK_SIZE_LIMIT {
      self.0.push(value);
      Ok(())
    } else {
      Err(PartialVMError::new(StatusCode::EXECUTION_STACK_OVERFLOW))
    }
  }

  /// Pop a `SymValue` off the stack or abort execution if the stack is empty.
  pub fn pop(&mut self) -> PartialVMResult<SymValue<'ctx>> {
    self
      .0
      .pop()
      .ok_or_else(|| PartialVMError::new(StatusCode::EMPTY_VALUE_STACK))
  }

  /// Pop a `SymValue` of a given type off the stack. Abort if the value is not of the given
  /// type or if the stack is empty.
  pub fn pop_as<T>(&mut self) -> PartialVMResult<T>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
  {
    self.pop()?.value_as()
  }

  /// Pop n values off the stack.
  pub fn popn(&mut self, n: u16) -> PartialVMResult<Vec<SymValue<'ctx>>> {
    let remaining_stack_size = self
      .0
      .len()
      .checked_sub(n as usize)
      .ok_or_else(|| PartialVMError::new(StatusCode::EMPTY_VALUE_STACK))?;
    let args = self.0.split_off(remaining_stack_size);
    Ok(args)
  }

  fn fork(&self) -> Self {
    SymStack(self.0.iter().map(|x| x.copy_value().unwrap()).collect())
  }
}

/// A call stack.
// TODO: should not be public
#[derive(Debug)]
pub struct SymCallStack<'ctx>(Vec<SymFrame<'ctx>>);

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

  fn current_location(&self) -> Location {
    let location_opt = self.0.last().map(|frame| frame.location());
    location_opt.unwrap_or(Location::Undefined)
  }
  
  fn fork(&self) -> Self {
    Self(self.0.iter().map(|frame| frame.fork()).collect())
  }
}

/// A `SymFrame` is the execution context for a function. It holds the locals of the function and
/// the function itself.
#[derive(Debug)]
struct SymFrame<'ctx> {
  z3_ctx: &'ctx Context,
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
    z3_ctx: &'ctx Context,
    function: Arc<Function>,
    ty_args: Vec<Type>,
    locals: SymLocals<'ctx>
  ) -> Self {
    SymFrame {
      z3_ctx,
      pc: 0,
      locals,
      function,
      ty_args,
    }
  }

  /// Execute a Move function until a return or a call opcode is found.
  fn execute_code<'r, 'l, R: RemoteCache>(
    &mut self,
    resolver: &Resolver,
    interpreter: &mut SymInterpreter<'ctx, 'r, 'l, R>,
    manager: &mut PluginManager<'_, 'ctx>
  ) -> VMResult<ExitCode<'ctx>> {
    self.execute_code_impl(resolver, interpreter, manager)
      .map_err(|e| {
        e.at_code_offset(self.function.index(), self.pc)
          .finish(self.location())
      })
  }
  
  fn execute_code_impl<'r, 'l, R: RemoteCache>(
    &mut self,
    resolver: &Resolver,
    interpreter: &mut SymInterpreter<'ctx, 'r, 'l, R>,
    manager: &mut PluginManager<'_, 'ctx>
  ) -> PartialVMResult<ExitCode<'ctx>> {
    let code = self.function.code();
    loop {
      for instruction in &code[self.pc as usize..] {
        // trace!(self.function.pretty_string(), self.pc, instruction);

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
          // TODO:
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
                PartialVMError::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
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
            let struct_tag = resolver.get_struct_tag(*sd_idx);
            interpreter
              .operand_stack
              .push(SymValue::from_sym_struct(SymStruct::pack(interpreter.solver.get_context(), &struct_tag, args)?))?;
          }
          Bytecode::PackGeneric(si_idx) => {
            let field_count = resolver.field_instantiation_count(*si_idx);
            let args = interpreter.operand_stack.popn(field_count)?;
            // let size = args.iter().fold(
            //   AbstractMemorySize::new(GasCarrier::from(field_count)),
            //   |acc, v| acc.add(v.size()),
            // );
            // gas!(instr: context, interpreter, Opcodes::PACK, size)?;
            let struct_tag = resolver.instantiate_generic_tag(*si_idx, self.ty_args())?;
            interpreter
              .operand_stack
              .push(SymValue::from_sym_struct(SymStruct::pack(interpreter.solver.get_context(), &struct_tag, args)?))?;
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
            interpreter.binop_bool(|l: SymBool<'ctx>, r| Ok(SymBool::or(self.z3_ctx, &[l, r])))?
          }
          Bytecode::And => {
            // gas!(const_instr: context, interpreter, Opcodes::AND)?;
            interpreter.binop_bool(|l: SymBool<'ctx>, r| Ok(SymBool::and(self.z3_ctx, &[l, r])))?
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
                PartialVMError::new(StatusCode::ABORTED)
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
                  sym_error_code,
                  self.function.pretty_string(),
                  self.pc,
                );
                Err(PartialVMError::new(StatusCode::ABORTED).with_message(msg))
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
          Bytecode::MutBorrowGlobal(sd_idx) | Bytecode::ImmBorrowGlobal(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.get_struct_type(*sd_idx);
            let _size = interpreter.borrow_global(addr, &ty)?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MUT_BORROW_GLOBAL,
            //   size
            // )?;
          }
          Bytecode::MutBorrowGlobalGeneric(si_idx)
          | Bytecode::ImmBorrowGlobalGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.instantiate_generic_type(*si_idx, self.ty_args())?;
            let _size = interpreter.borrow_global(addr, &ty)?;
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MUT_BORROW_GLOBAL_GENERIC,
            //   size
            // )?;
          }
          Bytecode::Exists(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.get_struct_type(*sd_idx);
            let _size = interpreter.exists(addr, &ty)?;
            // gas!(instr: context, interpreter, Opcodes::EXISTS, size)?;
          }
          Bytecode::ExistsGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.instantiate_generic_type(*si_idx, self.ty_args())?;
            let _size = interpreter.exists(addr, &ty)?;
            // gas!(instr: context, interpreter, Opcodes::EXISTS_GENERIC, size)?;
          }
          Bytecode::MoveFrom(sd_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.get_struct_type(*sd_idx);
            let _size = interpreter.move_from(addr, &ty)?;
            // TODO: Have this calculate before pulling in the data based upon
            // the size of the data that we are about to read in.
            // gas!(instr: context, interpreter, Opcodes::MOVE_FROM, size)?;
          }
          Bytecode::MoveFromGeneric(si_idx) => {
            let addr = interpreter.operand_stack.pop_as::<SymAccountAddress>()?.into_address()?;
            let ty = resolver.instantiate_generic_type(*si_idx, self.ty_args())?;
            let _size = interpreter.move_from(addr, &ty)?;
            // TODO: Have this calculate before pulling in the data based upon
            // the size of the data that we are about to read in.
            // gas!(
            //   instr: context,
            //   interpreter,
            //   Opcodes::MOVE_FROM_GENERIC,
            //   size
            // )?;
          }
          Bytecode::MoveTo(sd_idx) => {
            let resource = interpreter.operand_stack.pop()?;
            let signer_reference = interpreter.operand_stack.pop_as::<SymStructRef>()?;
            let addr = signer_reference
              .borrow_field(0)?
              .value_as::<SymReference>()?
              .read_ref()?
              .value_as::<SymAccountAddress>()?
              .into_address()?;
            let ty = resolver.get_struct_type(*sd_idx);
            let _size = interpreter.move_to(addr, &ty, resource)?;
            // gas!(instr: context, interpreter, Opcodes::MOVE_TO, size)?;
          }
          Bytecode::MoveToGeneric(si_idx) => {
            let resource = interpreter.operand_stack.pop()?;
            let signer_reference = interpreter.operand_stack.pop_as::<SymStructRef>()?;
            let addr = signer_reference
              .borrow_field(0)?
              .value_as::<SymReference>()?
              .read_ref()?
              .value_as::<SymAccountAddress>()?
              .into_address()?;
            let ty = resolver.instantiate_generic_type(*si_idx, self.ty_args())?;
            let _size = interpreter.move_to(addr, &ty, resource)?;
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
        self.pc += 1;
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
          return Err(PartialVMError::new(StatusCode::PC_OVERFLOW));
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

  fn location(&self) -> Location {
    match self.function.module_id() {
      None => Location::Script,
      Some(id) => Location::Module(id.clone()),
    }
  }

  fn fork(&self) -> Self {
    Self {
      z3_ctx: self.z3_ctx,
      pc: self.pc,
      function: self.function.clone(),
      ty_args: self.ty_args.clone(),
      locals: self.locals.fork(),
    }
  }
}
