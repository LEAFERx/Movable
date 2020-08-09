use crate::{
  plugin::Plugin,
  runtime::interpreter::SymInterpreter,
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use std::vec::Vec;

pub struct PluginManager<'a> {
  plugins: Vec<Box<dyn Plugin + 'a>>,
}

impl<'a> PluginManager<'a> {
  pub fn new() -> Self {
    Self {
      plugins: vec![],
    }
  }
  pub fn add_plugin(&mut self, p: impl Plugin + 'a) {
    self.plugins.push(Box::new(p));
  }

  pub(crate) fn before_execute_instruction<'ctx>(
    &self,
    interpreter: &mut SymInterpreter<'_, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()>{
    for plugin in self.plugins.iter() {
      plugin.on_before_execute_instrcution(interpreter, instruction)?;
    }
    Ok(())
  }
}