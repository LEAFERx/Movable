use bytecode_verifier::VerifiedModule;
use libra_types::{
  identifier::IdentStr,
  language_storage::ModuleId,
};
use std::marker::PhantomData;
use vm::{
  errors::*,
  file_format::{FunctionHandleIndex, SignatureToken},
};
use vm_cache_map::Arena;
use vm_runtime::{
  code_cache::module_cache::VMModuleCache,
  execution_context::InterpreterContext,
  loaded_data::{
    function::FunctionRef,
    loaded_module::LoadedModule,
  },
};
use vm_runtime_types::{loaded_data::types::Type, type_context::TypeContext};

use crate::{
  engine::solver::Solver,
  symbolic_vm::{
    interpreter::SymInterpreter,
    types::value::SymValue,
  },
};

pub struct SymVMRuntime<'ctx, 'alloc> {
  code_cache: VMModuleCache<'alloc>,

  phatom: PhantomData<&'ctx Solver<'ctx>>,
}

impl<'ctx, 'alloc> SymVMRuntime<'ctx, 'alloc> {
  pub fn new(allocator: &'alloc Arena<LoadedModule>) -> Self {
    SymVMRuntime {
      code_cache: VMModuleCache::new(allocator),
      phatom: PhantomData,
    }
  }

  pub fn cache_module(&mut self, module: VerifiedModule) {
    self.code_cache.cache_module(module);
  }

  pub fn resolve_function_ref(
    &self,
    caller_module: &LoadedModule,
    idx: FunctionHandleIndex,
    data_view: &dyn InterpreterContext,
  ) -> VMResult<FunctionRef<'alloc>> {
    self
      .code_cache
      .resolve_function_ref(caller_module, idx, data_view)
  }

  pub fn resolve_signature_token(
    &self,
    module: &LoadedModule,
    tok: &SignatureToken,
    type_context: &TypeContext,
    data_view: &dyn InterpreterContext,
  ) -> VMResult<Type> {
    self
      .code_cache
      .resolve_signature_token(module, tok, type_context, data_view)
  }

  pub fn get_loaded_module(
    &self,
    id: &ModuleId,
    data_view: &dyn InterpreterContext,
  ) -> VMResult<&'alloc LoadedModule> {
    self.code_cache.get_loaded_module(id, data_view)
  }

  pub fn execute_function(
    &self,
    solver: &'ctx Solver<'ctx>,
    interp_context: &mut dyn InterpreterContext,
    module: &ModuleId,
    function_name: &IdentStr,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    SymInterpreter::execute_function(
      solver,
      interp_context,
      self,
      module,
      function_name,
      args,
    )
  }
}
