use z3::{ast, ast::Ast, Context, Sort};

fn symbolic_u8_sort(ctx: &Context) -> Sort {
  Sort::bitvector(ctx, 8)
}

#[derive(Debug, Clone)]
pub struct SymByteArray<'ctx> {
  array: ast::Array<'ctx>,
  length: ast::Int<'ctx>
}

impl<'ctx> SymByteArray<'ctx> {
  pub fn new(ctx: &'ctx Context, prefix: &str) -> Self {
    Self {
      array: ast::Array::fresh_const(ctx, prefix, &Sort::int(ctx), &symbolic_u8_sort(ctx)),
      length: ast::Int::from_u64(ctx, 0),
    }
  }

  pub fn len(&self) -> &ast::Int<'ctx> {
    &self.length
  }

  pub fn equals(&self, other: &Self) -> ast::Bool<'ctx> {
    let res = self.array._eq(&other.array);
    res.and(&[&self.length._eq(&other.length)])
  }
}
