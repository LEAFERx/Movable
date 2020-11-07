use crate::{
  plugin::Plugin,
  runtime::{
    interpreter::SymInterpreter,
    loader::{Loader, Function},
  },
  state::vm_context::SymbolicVMContext,
  types::values::SymValue,
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use move_vm_types::loaded_data::runtime_types::Type;

use std::vec::Vec;

pub struct PluginManager<'a, 'ctx> {
  plugins: Vec<Box<dyn Plugin<'ctx> + 'a>>,
}

impl<'a, 'ctx> PluginManager<'a, 'ctx> {
  pub fn new() -> Self {
    Self {
      plugins: vec![],
    }
  }

  pub fn add_plugin(&mut self, p: impl Plugin<'ctx> + 'a) {
    self.plugins.push(Box::new(p));
  }

  pub(crate) fn before_execute_instruction<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()>{
    for plugin in self.plugins.iter() {
      plugin.on_before_execute_instrcution(interpreter, instruction)?;
    }
    Ok(())
  }

  pub(crate) fn before_call<'vtxn>(
    &self,
    vm_ctx: &SymbolicVMContext<'vtxn, 'ctx>,
    loader: &Loader,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    func: &Function,
    ty_args: Vec<Type>,
  ) -> VMResult<bool>{
    let mut result = false;
    for plugin in self.plugins.iter() {
      result = result || plugin.on_before_call(vm_ctx, loader, interpreter, func, ty_args.clone())?;
    }
    Ok(result)
  }

  pub(crate) fn before_execute(&self) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_before_execute()?;
    }
    Ok(())
  }

  pub(crate) fn after_execute<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_after_execute(interpreter, return_values)?;
    }
    Ok(())
  }
}