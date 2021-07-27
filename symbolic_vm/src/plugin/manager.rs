use crate::{
  plugin::{Plugin, PluginContext},
  runtime::{
    loader::{Loader, Function},
  },
  types::values::{SymValue, SymU64},
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use move_vm_types::loaded_data::runtime_types::Type;

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
    plugin_context: &mut dyn PluginContext<'ctx>,
    instruction: &Bytecode
  ) -> PartialVMResult<()>{
    for plugin in self.plugins.iter() {
      plugin.on_before_execute_instrcution(plugin_context, instruction)?;
    }
    Ok(())
  }

  pub(crate) fn before_call<'ctx>(
    &self,
    plugin_context: &mut dyn PluginContext<'ctx>,
    func: &Function,
    ty_args: Vec<Type>,
  ) -> PartialVMResult<bool>{
    let mut result = false;
    for plugin in self.plugins.iter() {
      result = result || plugin.on_before_call(plugin_context, func, ty_args.clone())?;
    }
    Ok(result)
  }

  pub(crate) fn before_execute<'ctx>(&self) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_before_execute()?;
    }
    Ok(())
  }

  pub(crate) fn after_execute<'ctx>(
    &self,
    plugin_context: &mut dyn PluginContext<'ctx>,
    return_values: &[SymValue<'ctx>],
  ) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_after_execute(plugin_context, return_values)?;
    }
    Ok(())
  }

  pub(crate) fn on_after_execute_user_abort<'ctx>(
    &self,
    plugin_context: &mut dyn PluginContext<'ctx>,
    code: &SymU64<'ctx>,
  ) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_after_execute_user_abort(plugin_context, code)?;
    }
    Ok(())
  }

  pub(crate) fn on_after_execute_abort<'ctx>(
    &self,
    plugin_context: &mut dyn PluginContext<'ctx>,
    err: &VMError,
  ) -> VMResult<()> {
    for plugin in self.plugins.iter() {
      plugin.on_after_execute_abort(plugin_context, err)?;
    }
    Ok(())
  }
}