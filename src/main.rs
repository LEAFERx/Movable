use libra_types::{
  transaction::Module,
};
use move_core_types::identifier::IdentStr;
use vm::{
  CompiledModule,
};

use std::{
  fs,
  io::BufReader,
  path::{Path, PathBuf},
};
use structopt::StructOpt;

extern crate engine;
use engine::Engine;

#[derive(Debug, StructOpt)]
struct Args {
  #[structopt(parse(from_os_str))]
  pub source: PathBuf,
  #[structopt(name = "function name", short, long)]
  pub func: String,
}

fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> CompiledModule {
  // let bytecode_file = File::open(bytecode_path).expect("Failed to open bytecode file");
  // let bytecode_reader = BufReader::new(bytecode_file);
  // let bytecode_json: Module = serde_json::from_reader(bytecode_reader)
  //   .expect("Failed to parse json format. File may be corrupted.");
  // CompiledModule::deserialize(&bytecode_json.code())
  //   .expect("Failed to read bytecode. File may be corrupted.")
  let module_bytes = fs::read(bytecode_path).expect("Failed to open bytecode file");
  CompiledModule::deserialize(module_bytes.as_slice())
    .expect("Failed to read bytecode. File may be corrupted.")
}

fn main() {
  env_logger::init();

  let args = Args::from_args();
  let path = Path::new(&args.source);
  let function_name = IdentStr::new(args.func.as_str()).unwrap();

  let module = read_bytecode(path);

  let mut engine = Engine::from_genesis();
  engine.add_module(&module.self_id(), &module);
  engine.execute_function(&module.self_id(), &function_name);
}
