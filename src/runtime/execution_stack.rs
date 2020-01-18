use crate::runtime::{
  frame::Frame,
  value::{Locals, Value},
};

use libra_types::vm_error::StatusCode;
use vm::errors::{VMResult, vm_error, Location};
use vm_runtime::{
  code_cache::module_cache::ModuleCache,
  loaded_data::function::{
    FunctionRef,
    FunctionReference,
  }
};

pub struct ExecutionStack<'ctx, P>
where
  P: ModuleCache<'ctx>
{
  stack: Vec<Value<'ctx>>,
  call_stack: Vec<Frame<'ctx>>,
  pub module_cache: P,
}

impl<'ctx, P> ExecutionStack<'ctx, P>
where
  P: ModuleCache<'ctx>
{
  pub fn new(module_cache: P) -> Self {
    ExecutionStack {
      stack: vec![],
      call_stack: vec![],
      module_cache,
    }
  }

  pub fn push_call(&mut self, function: FunctionRef<'ctx>) -> VMResult<()> {
    let mut locals = Locals::new(function.local_count());
    let arg_count = function.arg_count();
    for i in 0..arg_count {
      locals.store_loc(arg_count - i - 1, self.pop()?)?;
    }
    self.call_stack.push(Frame::new(function, locals));
    Ok(())
  }

  pub fn pop_call(&mut self) -> VMResult<()> {
    self
      .call_stack
      .pop()
      .ok_or_else(|| vm_error(Location::default(), StatusCode::EMPTY_CALL_STACK))?;
    Ok(())
  }

  pub fn top_frame(&self) -> VMResult<&Frame<'ctx>> {
    Ok(
      self
        .call_stack
        .last()
        .ok_or_else(|| vm_error(Location::default(), StatusCode::EMPTY_CALL_STACK))?,
    )
  }

  pub fn top_frame_mut(&mut self) -> VMResult<&mut Frame<'ctx>> {
    Ok(
      self
        .call_stack
        .last_mut()
        .ok_or_else(|| vm_error(Location::default(), StatusCode::EMPTY_CALL_STACK))?,
    )
  }

  pub fn is_call_stack_empty(&self) -> bool {
    self.call_stack.is_empty()
  }

  pub fn location(&self) -> VMResult<Location> {
    Ok(self.top_frame()?.into())
  }

  pub fn push(&mut self, value: Value<'ctx>) -> VMResult<()> {
    self.stack.push(value);
    Ok(())
  }

  pub fn peek(&self) -> VMResult<&Value<'ctx>> {
    Ok(self.stack.last().ok_or_else(|| {
      vm_error(
        self.location().unwrap_or_default(),
        StatusCode::EMPTY_VALUE_STACK,
      )
    })?)
  }

  pub fn pop(&mut self) -> VMResult<Value<'ctx>> {
    Ok(self.stack.pop().ok_or_else(|| {
      vm_error(
        self.location().unwrap_or_default(),
        StatusCode::EMPTY_VALUE_STACK,
      )
    })?)
  }

  pub fn pop_as<T>(&mut self) -> VMResult<T>
  where
    Option<T>: From<Value<'ctx>>,
  {
    let top = self.pop()?.value_as();
    top.ok_or_else(|| vm_error(self.location().unwrap_or_default(), StatusCode::TYPE_ERROR))
  }

  pub fn popn(&mut self, n: u16) -> VMResult<Vec<Value<'ctx>>> {
    let remaining_stack_size = self
      .stack
      .len()
      .checked_sub(n as usize)
      .ok_or_else(|| {
        vm_error(
          self.location().unwrap_or_default(),
          StatusCode::EMPTY_VALUE_STACK,
        )
      })?;
    let args = self.stack.split_off(remaining_stack_size);
    Ok(args)
  }
  
  pub fn call_stack_height(&self) -> usize {
    self.call_stack.len()
  }
}
