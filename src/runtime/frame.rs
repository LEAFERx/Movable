use super::value::{Locals, Value};
use std::fmt;
use vm::{
  errors::{Location, VMResult},
  file_format::{Bytecode, CodeOffset, LocalIndex},
};
use vm_runtime::loaded_data::{
  loaded_module::LoadedModule,
  function::{
    FunctionRef,
    FunctionReference
  }
};

pub struct Frame<'ctx> {
  pc: u16,
  locals: Locals<'ctx>,
  function: FunctionRef<'ctx>,
}

impl<'ctx> Frame<'ctx> {
  pub fn new(
    function: FunctionRef<'ctx>,
    locals: Locals<'ctx>,
  ) -> Self {
    Frame {
      pc: 0,
      locals,
      function,
    }
  }

  pub fn code_definition(&self) -> &'ctx [Bytecode] {
    self.function.code_definition()
  }

  pub fn save_pc(&mut self, offset: CodeOffset) {
    self.pc = offset;
  }

  pub fn get_pc(&self) -> u16 {
    self.pc
  }
  
  pub fn module(&self) -> &'ctx LoadedModule {
    self.function.module()
  }

  pub fn copy_loc(&self, idx: LocalIndex) -> VMResult<Value<'ctx>> {
    self.locals.copy_loc(idx as usize)
  }

  pub fn move_loc(&mut self, idx: LocalIndex) -> VMResult<Value<'ctx>> {
    self.locals.move_loc(idx as usize)
  }

  pub fn store_loc(&mut self, idx: LocalIndex, value: Value<'ctx>) -> VMResult<()> {
    self.locals.store_loc(idx as usize, value)
  }
}

impl<'ctx> Into<Location> for &Frame<'ctx> {
  fn into(self) -> Location {
    Location::new()
  }
}

impl<'ctx> fmt::Debug for Frame<'ctx> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "\n[")?;
    write!(f, "\n\tFunction: {}", self.function.name())?;
    write!(f, "\n\tLocals: {:?}", self.locals)?;
    write!(f, "\n]")
  }
}
