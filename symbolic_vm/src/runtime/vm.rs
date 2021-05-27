use move_vm_runtime::data_cache::RemoteCache;
use z3::Context;
use crate::{
  runtime::{
    runtime::VMRuntime,
    session::Session,
  },
};

pub struct SymbolicVM<'ctx> {
  runtime: VMRuntime<'ctx>,
  z3_ctx: &'ctx Context,
}

impl<'ctx> SymbolicVM<'ctx> {
  pub fn new(z3_ctx: &'ctx Context) -> Self {
    Self {
      runtime: VMRuntime::new(),
      z3_ctx,
    }
  }

  pub fn new_session<'r, R: RemoteCache>(&self, remote: &'r R) -> Session<'ctx, 'r, '_, R> {
    self.runtime.new_session(self.z3_ctx, remote)
  }
}

// impl Default for SymbolicVM {
//   fn default() -> Self {
//     Self::new()
//   }
// }
