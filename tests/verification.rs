use move_core_types::identifier::IdentStr;
use vm::CompiledModule;
use std::{
  fs,
  path::Path,
};
use engine::Engine;

fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> Vec<u8> {
  fs::read(bytecode_path).expect("Failed to open bytecode file")
}

fn exec(path: &str, func: &str) {
  env_logger::init();
  let path = Path::new(path);
  let function_name = IdentStr::new(func).unwrap();
  let blob = read_bytecode(path);
  let module = CompiledModule::deserialize(blob.as_slice())
    .expect("Failed to deserialize bytecode. File may be corrupted.");
  let mut engine = Engine::from_genesis();
  engine.add_module(&module.self_id(), blob);
  engine.execute_function(&module.self_id(), &function_name);
}

#[test]
fn abs() {
  exec("testsuites/abs.mv", "f");
}