use z3::{ast, ast::Ast, Context, Sort};

use crate::{
  engine::solver::Solver,
  symbolic_vm::types::primitives::SymBool,
};

fn symbolic_u8_sort(ctx: &Context) -> Sort {
  Sort::bitvector(ctx, 8)
}

#[derive(Debug, Clone)]
pub struct SymByteArray<'ctx> {
  array: ast::Array<'ctx>,
  length: ast::Int<'ctx>
}

impl<'ctx> SymByteArray<'ctx> {
  pub fn new(solver: &Solver<'ctx>, prefix: &str) -> Self {
    let ctx = solver.ctx();
    Self {
      array: ast::Array::fresh_const(ctx, prefix, &Sort::int(ctx), &symbolic_u8_sort(ctx)),
      length: ast::Int::from_u64(ctx, 0),
    }
  }

  pub fn len(&self) -> &ast::Int<'ctx> {
    &self.length
  }

  pub fn equals(&self, other: &Self) -> SymBool<'ctx> {
    let res = self.array._eq(&other.array);
    SymBool::from_ast(res.and(&[&self.length._eq(&other.length)]))
  }
}
