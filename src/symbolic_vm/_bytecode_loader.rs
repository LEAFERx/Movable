use anyhow::Result;
use libra_types::{
  transaction::Module
};
use vm_runtime::{
  code_cache::module_cache::VMModuleCache
};
use std::{
  fs,
};

pub struct BytecodeLoader {
  
}

pub fn read_bytecode(path: &str) -> Result<Module> {
  let module = serde_json::from_slice(&fs::read(path)?)?;
  Ok(module)
}