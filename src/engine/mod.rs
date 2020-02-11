use libra_types::{
  account_address::ADDRESS_LENGTH,
};

use serde::{Serialize, Deserialize};

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
struct ModuleList {
  address: [u8; ADDRESS_LENGTH],
  modules: Vec<String>,
}

#[derive(Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct EngineConfig {
  module_list: Vec<ModuleList>,
}
