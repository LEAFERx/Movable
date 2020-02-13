use bytecode_verifier::VerifiedModule;
use libra_types::{
  identifier::IdentStr,
  language_storage::ModuleId
};
use std::{fs::File, io::BufReader, path::Path, marker::PhantomData};
use vm::{
  errors::*,
  file_format::{CompiledModule, FunctionHandleIndex, SignatureToken},
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
use libra_types::transaction::Module;
use z3::{
  Context
};

use crate::symbolic_vm::{
  interpreter::SymInterpreter,
};

fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> VerifiedModule {
  let bytecode_file = File::open(bytecode_path).expect("Failed to open bytecode file");
  let bytecode_reader = BufReader::new(bytecode_file);
  let bytecode_json: Module = serde_json::from_reader(bytecode_reader)
    .expect("Failed to parse json format. File may be corrupted.");
  let module = CompiledModule::deserialize(&bytecode_json.code())
    .expect("Failed to read bytecode. File may be corrupted.");
  VerifiedModule::new(module)
    .expect("Failed to verify module. This module may not be verified correctly.")
}

pub struct SymVMRuntime<'ctx, 'alloc> {
  code_cache: VMModuleCache<'alloc>,

  phatom: PhantomData<&'ctx Context>,
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

  pub fn load_module_from_path<P: AsRef<Path>>(&mut self, path: P) {
    self.cache_module(read_bytecode(path))
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
    ctx: &'ctx Context,
    interp_context: &mut dyn InterpreterContext,
    module: &ModuleId,
    function_name: &IdentStr,
  ) -> VMResult<()> {
    SymInterpreter::execute_function(
      ctx,
      interp_context,
      self,
      module,
      function_name,
    )
  }
}
