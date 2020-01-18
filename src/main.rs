use libra_types::{
  identifier::IdentStr,
  language_storage::ModuleId,
};
use serde::Deserialize;
use std::{
  error::Error,
  fs::File,
  io::BufReader,
  path::{Path, PathBuf},
};
use structopt::StructOpt;
use vm::{
  access::ModuleAccess,
  file_format::{
    CompiledModule,
  },
};
use vm_runtime::{
  loaded_data::{
    loaded_module::LoadedModule,
    function::{
      FunctionRef,
      FunctionReference,
    },
  },
  code_cache::{
    module_cache::{
      ModuleCache,
      VMModuleCache,
      BlockModuleCache,
    },
    module_adapter::{
      FakeFetcher,
    },
  },
};
use vm_cache_map::Arena;
// use bytecode_verifier::verifier::VerifiedModule;

use movable::runtime::{
  value::{Locals, Value},
  execution_stack::ExecutionStack,
  frame::Frame,
  executor::Executor,
};
use z3::{ast, Config, Context};

#[derive(Debug, StructOpt)]
struct Args {
  #[structopt(parse(from_os_str))]
  pub source: PathBuf,
  #[structopt(name = "function name", short, long)]
  pub func: String,
}

#[derive(Deserialize)]
struct ModuleBytecode {
  code: Vec<u8>,
}

// fn load_bytecode<'a, P: AsRef<Path>>(bytecode_path: P) -> Result<LoadedModule, Box<dyn Error>> {
//   let bytecode_file = File::open(bytecode_path)?;
//   let bytecode_reader = BufReader::new(bytecode_file);
//   let bytecode_json: ModuleBytecode = serde_json::from_reader(bytecode_reader)?;
//   let module = CompiledModule::deserialize(&bytecode_json.code).expect("Failed to read bytecode. File may be corrupted.");
//   let module = VerifiedModule::new(module).expect("Failed to verify module");
//   let module = LoadedModule::new(module);
//   Ok(module)
// }

fn load_bytecode<'a, P: AsRef<Path>>(bytecode_path: P) -> Result<(CompiledModule, ModuleId), Box<dyn Error>> {
  let bytecode_file = File::open(bytecode_path)?;
  let bytecode_reader = BufReader::new(bytecode_file);
  let bytecode_json: ModuleBytecode = serde_json::from_reader(bytecode_reader)?;
  let module = CompiledModule::deserialize(&bytecode_json.code).expect("Failed to read bytecode. File may be corrupted.");
  let id = module.self_id();
  Ok((module, id))
}

fn load_modules<'a>(vm_cache: &'a VMModuleCache<'a>, modules: Vec<CompiledModule>) -> BlockModuleCache<'a, 'a, FakeFetcher> {
  let module_fetcher = FakeFetcher::new(modules);
  BlockModuleCache::new(vm_cache, module_fetcher)
}

fn main() {
  let args = Args::from_args();
  let path = Path::new(&args.source);
  let function_name = IdentStr::new(args.func.as_str()).unwrap();

  let allocator = Arena::new();
  let vm_cache = VMModuleCache::new(&allocator);
  let (module, id) = load_bytecode(path).unwrap();
  let module_cache = load_modules(&vm_cache, vec![module]);

  // let function = FunctionRef::new(&module, *module.function_defs_table.get(function_name).unwrap());
  let loaded_module = module_cache.get_loaded_module(&id)
    .expect("VM Interal Error").expect("Module Not Found");
  let function_def_index = loaded_module.function_defs_table.get(function_name).unwrap();
  println!("{:#?}", loaded_module.function_def_at(*function_def_index).code);
  let function_handle_index = loaded_module.function_def_at(*function_def_index).function;
  let function = module_cache.resolve_function_ref(loaded_module, function_handle_index).unwrap().unwrap();

  let config = Config::new();
  let context = Context::new(&config);

  let mut executor = Executor::new(&context, &module_cache);
  let (_symbol_count, model, return_values) = executor.execute_function(function).unwrap();
  println!("------------------------------");
  println!("{}", model);
  println!("The function given above args returns {:?}", return_values);
  println!("------------------------------\n");
}
