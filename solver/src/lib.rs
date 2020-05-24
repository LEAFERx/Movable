use z3::{ast::Bool, Context as Z3Context, Model as Z3Model, SatResult, Solver as Z3Solver};

use std::fmt;

/// A Z3Solver with a pointer to its context
pub struct Solver<'ctx> {
    ctx: &'ctx Z3Context,
    solver: Z3Solver<'ctx>,
}

impl<'ctx> Solver<'ctx> {
    pub fn new(ctx: &'ctx Z3Context) -> Self {
        Solver {
            ctx,
            solver: Z3Solver::new(ctx),
        }
    }
    pub fn ctx(&self) -> &'ctx Z3Context {
        self.ctx
    }
    pub fn assert(&self, cond: &Bool<'ctx>) {
        self.solver.assert(cond);
    }
    pub fn check(&self) -> SatResult {
        self.solver.check()
    }
    pub fn get_model(&self) -> Z3Model {
        self.solver.get_model()
    }
}

impl<'ctx> PartialEq for Solver<'ctx> {
    fn eq(&self, other: &Self) -> bool {
        self.ctx() == other.ctx()
    }
}

impl<'ctx> Eq for Solver<'ctx> {}

impl<'ctx> fmt::Debug for Solver<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?})", self.ctx())
    }
}
