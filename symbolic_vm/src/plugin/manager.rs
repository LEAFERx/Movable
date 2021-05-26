use crate::{
  plugin::{Plugin, PluginContext},
  runtime::{
    loader::{Loader, Function},
  },
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

  pub(crate) fn before_execute_instruction(
    &self,
    plugin_context: &dyn PluginContext<'ctx>,
    instruction: &Bytecode
  ) -> PartialVMResult<()>{
    for plugin in self.plugins.iter() {
      plugin.on_before_execute_instrcution(plugin_context, instruction)?;
    }
    Ok(())
  }

  pub(crate) fn before_call(
    &self,
    loader: &Loader,
    plugin_context: &dyn PluginContext<'ctx>,
    func: &Function,
    ty_args: Vec<Type>,
  ) -> PartialVMResult<bool>{
    let mut result = false;
    for plugin in self.plugins.iter() {
      result = result || plugin.on_before_call(loader, plugin_context, func, ty_args.clone())?;
    }
    Ok(result)
  }

  pub(crate) fn before_execute(&self) -> PartialVMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_before_execute()?;
    }
    Ok(())
  }

  pub(crate) fn after_execute(
    &self,
    plugin_context: &dyn PluginContext<'ctx>,
    return_values: &[SymValue<'ctx>],
  ) -> PartialVMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_after_execute(plugin_context, return_values)?;
    }
    Ok(())
  }
}