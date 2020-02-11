use libra_types::{
  identifier::IdentStr,
  language_storage::{ModuleId, StructTag, TypeTag},
  vm_error::{StatusCode, StatusType, VMStatus},
};
use libra_logger::prelude::*;
use vm::{
  access::ModuleAccess,
  errors::*,
  file_format::{
    Bytecode, FunctionHandleIndex, LocalIndex, LocalsSignatureIndex, SignatureToken,
    StructDefinitionIndex,
  },
};
use vm_runtime::{
  execution_context::InterpreterContext,
  loaded_data::{
    function::{FunctionRef, FunctionReference},
    loaded_module::LoadedModule,
  },
};
use vm_runtime_types::loaded_data::{struct_def::StructDef, types::Type};

use z3::Context;

use std::marker::PhantomData;

use crate::symbolic_vm::{
  runtime::SymVMRuntime,
  types::value::{SymLocals, SymValue},
};

fn derive_type_tag(
  module: &impl ModuleAccess,
  type_actual_tags: &[TypeTag],
  ty: &SignatureToken,
) -> VMResult<TypeTag> {
  use SignatureToken::*;

  match ty {
    Bool => Ok(TypeTag::Bool),
    Address => Ok(TypeTag::Address),
    U8 => Ok(TypeTag::U8),
    U64 => Ok(TypeTag::U64),
    U128 => Ok(TypeTag::U128),
    ByteArray => Ok(TypeTag::ByteArray),
    TypeParameter(idx) => type_actual_tags
      .get(*idx as usize)
      .ok_or_else(|| {
        VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION)
          .with_message("Cannot derive type tag: type parameter index out of bounds.".to_string())
      })
      .map(|inner| inner.clone()),
    Reference(_) | MutableReference(_) => Err(
      VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION)
        .with_message("Cannot derive type tag for references.".to_string()),
    ),
    Struct(idx, struct_type_actuals) => {
      let struct_type_actuals_tags = struct_type_actuals
        .iter()
        .map(|ty| derive_type_tag(module, type_actual_tags, ty))
        .collect::<VMResult<Vec<_>>>()?;
      let struct_handle = module.struct_handle_at(*idx);
      let struct_name = module.identifier_at(struct_handle.name);
      let module_handle = module.module_handle_at(struct_handle.module);
      let module_address = module.address_at(module_handle.address);
      let module_name = module.identifier_at(module_handle.name);
      Ok(TypeTag::Struct(StructTag {
        address: *module_address,
        module: module_name.into(),
        name: struct_name.into(),
        type_params: struct_type_actuals_tags,
      }))
    }
  }
}

pub struct SymInterpreter<'vtxn> {
  operand_stack: SymStack<'vtxn>,
  call_stack: CallStack<'vtxn>,
}

impl<'vtxn> SymInterpreter<'vtxn> {
  pub fn execute_function(
    ctx: &'vtxn Context,
    interp_context: &mut dyn InterpreterContext,
    runtime: &'vtxn SymVMRuntime<'_>,
    module: &ModuleId,
    function_name: &IdentStr,
    args: Vec<SymValue<'vtxn>>,
  ) -> VMResult<()> {
    let mut interp = Self::new();
    let loaded_module = runtime.get_loaded_module(module, interp_context)?;
    let func_idx = loaded_module
      .function_defs_table
      .get(function_name)
      .ok_or_else(|| VMStatus::new(StatusCode::LINKER_ERROR))?;
    let func = FunctionRef::new(loaded_module, *func_idx);

    interp.execute(ctx, runtime, interp_context, func, args)
  }

  fn new() -> Self {
    SymInterpreter {
      operand_stack: SymStack::new(),
      call_stack: CallStack::new(),
    }
  }

  fn execute(
    &mut self,
    ctx: &'vtxn Context,
    runtime: &'vtxn SymVMRuntime<'_>,
    interp_context: &mut dyn InterpreterContext,
    function: FunctionRef<'vtxn>,
    args: Vec<SymValue<'vtxn>>,
  ) -> VMResult<()> {
    let prefix = "TargetFuncArgs";
    let mut locals = SymLocals::new(function.local_count());
    for (i, value) in args.into_iter().enumerate() {
      locals.store_loc(i, value)?;
    }
    let mut current_frame = Frame::new(function, vec![], vec![], locals);
    loop {
      let code = current_frame.code_definition();
      let exit_code = self
        .execute_code_unit(ctx, runtime, interp_context, &mut current_frame, code)
        .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
      match exit_code {
        ExitCode::Return => {
          if let Some(frame) = self.call_stack.pop() {
            current_frame = frame;
          } else {
            return Err(self.unreachable("call stack cannot be empty", &current_frame));
          }
        }
        ExitCode::Call(idx, type_actuals_idx) => unimplemented!(),
        ExitCode::BrTrue => unimplemented!(),
        ExitCode::BrFalse => unimplemented!(),
      }
    }
  }

  fn execute_code_unit(
    &mut self,
    ctx: &'vtxn Context,
    runtime: &'vtxn SymVMRuntime<'_>,
    interp_context: &mut dyn InterpreterContext,
    frame: &mut Frame<'vtxn, FunctionRef<'vtxn>>,
    code: &[Bytecode],
  ) -> VMResult<ExitCode> {
    unimplemented!()
  }

  fn binop<F, T>(&mut self, f: F) -> VMResult<()>
  where
    VMResult<T>: From<SymValue<'vtxn>>,
    F: FnOnce(T, T) -> VMResult<SymValue<'vtxn>>,
  {
    let rhs = self.operand_stack.pop_as::<T>()?;
    let lhs = self.operand_stack.pop_as::<T>()?;
    let result = f(lhs, rhs)?;
    self.operand_stack.push(result)
  }

  //
  // Debugging and logging helpers.
  //

  /// Given an `VMStatus` generate a core dump if the error is an `InvariantViolation`.
  fn maybe_core_dump(
    &self,
    mut err: VMStatus,
    current_frame: &Frame<'vtxn, FunctionRef<'vtxn>>,
  ) -> VMStatus {
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

  /// Generate a string which is the status of the interpreter: call stack, current bytecode
  /// stream, locals and operand stack.
  ///
  /// It is used when generating a core dump but can be used for debugging of the interpreter.
  /// It will be exposed via a debug module to give developers a way to print the internals
  /// of an execution.
  fn get_internal_state(&self, current_frame: &Frame<'vtxn, FunctionRef<'vtxn>>) -> String {
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
    let code = current_frame.code_definition();
    let pc = current_frame.pc as usize;
    if pc < code.len() {
      let mut i = 0;
      for bytecode in &code[0..pc] {
        internal_state.push_str(format!("{}> {:?}\n", i, bytecode).as_str());
        i += 1;
      }
      internal_state.push_str(format!("{}* {:?}\n", i, code[pc]).as_str());
    }
    // internal_state.push_str(format!("Locals:\n{}", current_frame.locals.pretty_string()).as_str());
    internal_state.push_str(format!("Locals:\n{:?}", current_frame.locals).as_str());
    internal_state.push_str("Operand Stack:\n");
    for value in &self.operand_stack.0 {
      // internal_state.push_str(format!("{}\n", value.pretty_string()).as_str());
      internal_state.push_str(format!("{:?}\n", value).as_str());
    }
    internal_state
  }

  /// Generate a core dump and an `UNREACHABLE` invariant violation.
  fn unreachable(&self, msg: &str, current_frame: &Frame<'vtxn, FunctionRef<'vtxn>>) -> VMStatus {
    let err = VMStatus::new(StatusCode::UNREACHABLE).with_message(msg.to_string());
    self.maybe_core_dump(err, current_frame)
  }
}

const OPERAND_STACK_SIZE_LIMIT: usize = 1024;
const CALL_STACK_SIZE_LIMIT: usize = 1024;

#[derive(Debug)]
struct SymStack<'vtxn>(Vec<SymValue<'vtxn>>);

impl<'vtxn> SymStack<'vtxn> {
  /// Create a new empty operand stack.
  fn new() -> Self {
    SymStack(vec![])
  }

  /// Push a `Value` on the stack if the max stack size has not been reached. Abort execution
  /// otherwise.
  fn push(&mut self, value: SymValue<'vtxn>) -> VMResult<()> {
    if self.0.len() < OPERAND_STACK_SIZE_LIMIT {
      self.0.push(value);
      Ok(())
    } else {
      Err(VMStatus::new(StatusCode::EXECUTION_STACK_OVERFLOW))
    }
  }

  /// Pop a `Value` off the stack or abort execution if the stack is empty.
  fn pop(&mut self) -> VMResult<SymValue<'vtxn>> {
    self
      .0
      .pop()
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))
  }

  /// Pop a `Value` of a given type off the stack. Abort if the value is not of the given
  /// type or if the stack is empty.
  fn pop_as<T>(&mut self) -> VMResult<T>
  where
    VMResult<T>: From<SymValue<'vtxn>>,
  {
    self.pop()?.value_as()
  }

  /// Pop n values off the stack.
  fn popn(&mut self, n: u16) -> VMResult<Vec<SymValue<'vtxn>>> {
    let remaining_stack_size = self
      .0
      .len()
      .checked_sub(n as usize)
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))?;
    let args = self.0.split_off(remaining_stack_size);
    Ok(args)
  }
}

#[derive(Debug)]
struct CallStack<'vtxn>(Vec<Frame<'vtxn, FunctionRef<'vtxn>>>);

impl<'vtxn> CallStack<'vtxn> {
  /// Create a new empty call stack.
  fn new() -> Self {
    CallStack(vec![])
  }

  /// Push a `Frame` on the call stack.
  fn push(
    &mut self,
    frame: Frame<'vtxn, FunctionRef<'vtxn>>,
  ) -> ::std::result::Result<(), Frame<'vtxn, FunctionRef<'vtxn>>> {
    if self.0.len() < CALL_STACK_SIZE_LIMIT {
      self.0.push(frame);
      Ok(())
    } else {
      Err(frame)
    }
  }

  /// Pop a `Frame` off the call stack.
  fn pop(&mut self) -> Option<Frame<'vtxn, FunctionRef<'vtxn>>> {
    self.0.pop()
  }
}

#[derive(Debug)]
struct Frame<'vtxn, F: 'vtxn> {
  pc: u16,
  locals: SymLocals<'vtxn>,
  function: F,
  type_actual_tags: Vec<TypeTag>,
  type_actuals: Vec<Type>,
  phantom: PhantomData<&'vtxn F>,
}

#[derive(Debug)]
enum ExitCode {
  /// A `Return` opcode was found.
  Return,
  /// A `Call` opcode was found.
  Call(FunctionHandleIndex, LocalsSignatureIndex),
  /// A `BrTrue` opcode was found.
  BrTrue,
  /// A `BrFalse` opcode was found.
  BrFalse,
}

impl<'vtxn, F> Frame<'vtxn, F>
where
  F: FunctionReference<'vtxn>,
{
  /// Create a new `Frame` given a `FunctionReference` and the function `Locals`.
  ///
  /// The locals must be loaded before calling this.
  fn new(
    function: F,
    type_actual_tags: Vec<TypeTag>,
    type_actuals: Vec<Type>,
    locals: SymLocals<'vtxn>,
  ) -> Self {
    Frame {
      pc: 0,
      locals,
      function,
      type_actual_tags,
      type_actuals,
      phantom: PhantomData,
    }
  }

  /// Return the code stream of this function.
  fn code_definition(&self) -> &'vtxn [Bytecode] {
    self.function.code_definition()
  }

  /// Return the `LoadedModule` this function lives in.
  fn module(&self) -> &'vtxn LoadedModule {
    self.function.module()
  }

  /// Copy a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn copy_loc(&self, idx: LocalIndex) -> VMResult<SymValue<'vtxn>> {
    self.locals.copy_loc(idx as usize)
  }

  /// Move a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn move_loc(&mut self, idx: LocalIndex) -> VMResult<SymValue<'vtxn>> {
    self.locals.move_loc(idx as usize)
  }

  /// Store a `Value` into a local at the given index. Return an error if the index is
  /// out of bounds.
  fn store_loc(&mut self, idx: LocalIndex, value: SymValue<'vtxn>) -> VMResult<()> {
    self.locals.store_loc(idx as usize, value)
  }

  /// Borrow a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn borrow_loc(&mut self, idx: LocalIndex) -> VMResult<SymValue<'vtxn>> {
    self.locals.borrow_loc(idx as usize)
  }

  fn type_actual_tags(&self) -> &[TypeTag] {
    &self.type_actual_tags
  }

  fn type_actuals(&self) -> &[Type] {
    &self.type_actuals
  }
}
