use move_vm_runtime::data_cache::RemoteCache;
// use z3::Context;
use crate::{
  runtime::{
    context::Context,
    runtime::VMRuntime,
    session::Session,
  },
};

pub struct SymbolicVM<'ctx> {
  runtime: VMRuntime<'ctx>,
  ctx: &'ctx Context<'ctx>,
}

impl<'ctx> SymbolicVM<'ctx> {
  pub fn new(ctx: &'ctx Context<'ctx>) -> Self {
    Self {
      runtime: VMRuntime::new(),
      ctx,
    }
  }

  pub fn new_session<'r, R: RemoteCache>(&self, remote: &'r R) -> Session<'ctx, 'r, '_, R> {
    self.runtime.new_session(self.ctx, remote)
  }
}

// impl Default for SymbolicVM {
//   fn default() -> Self {
//     Self::new()
//   }
// }
