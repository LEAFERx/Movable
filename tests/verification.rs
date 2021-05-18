use move_core_types::identifier::IdentStr;
use vm::CompiledModule;
use std::{
  fs,
  path::Path,
};
use engine::Engine;

fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> CompiledModule {
  let module_bytes = fs::read(bytecode_path).expect("Failed to open bytecode file");
  CompiledModule::deserialize(module_bytes.as_slice())
    .expect("Failed to read bytecode. File may be corrupted.")
}

fn exec(path: &str, func: &str) {
  env_logger::init();
  let path = Path::new(path);
  let function_name = IdentStr::new(func).unwrap();
  let module = read_bytecode(path);
  let mut engine = Engine::from_genesis();
  engine.add_module(&module.self_id(), &module);
  engine.execute_function(&module.self_id(), &function_name);
}

#[test]
fn abs() {
  exec("testsuites/abs.mv", "f");
}