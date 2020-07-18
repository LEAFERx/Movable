use crate::types::interpreter_context::SymInterpreterContext;
use crate::{
    engine::solver::Solver,
    loader::{Function, Loader, Resolver},
    symbolic_vm::{interpreter::SymInterpreter, runtime::SymVMRuntime, types::value::SymValue},
};
use nix::unistd::{fork, ForkResult};
use solver::Solver;
use std::{clone::Clone, marker::PhantomData, process::exit, sync::Arc};
use vm::errors::VMResult;
use vm::file_format::{CodeOffset, FunctionHandleIndex, FunctionInstantiationIndex};
use z3::ast::Dynamic;
use z3::{ast, Context as Z3Context, Model as Z3Model, SatResult, Solver as Z3Solver};

/***************************************************************************************
*
* Plugin Manager
*
*   Implementation of the Plugin hook trait for single line code integer check, function check
*   and transaction check.
*
**************************************************************************************/

enum PluginError<'ctx> {
    Return,
    Call(FunctionHandleIndex),
    CallGeneric(FunctionInstantiationIndex),
    Branch(bool, SymBool<'ctx>, CodeOffset),
}

/***************************************************************************************
*
* Execution Plugin
*
*   trait
*   and transaction check.
*
**************************************************************************************/

pub struct ExecutionPlugin<'ctx> {
    pre: &'ctx Z3Context,
    post: &'ctx Z3Context,
    solver: Z3Solver<'ctx>,
}

impl<'ctx> ExecutionPlugin<'ctx> {
    fn new(ctx: &'ctx Z3Context) -> Self {
        ExecutionPlugin {
            pre,
            post,
            solver: Z3Solver::new(ctx),
        }
    }
    pub fn pre(&self) -> &'ctx Z3Context {
        self.pre
    }
    pub fn post(&self) -> &'ctx Z3Context {
        self.post
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
    pub fn ExecutionPluginHook(
        &mut self,
        solver: &'ctx Solver<'ctx>,
        interpreter: &mut SymInterpreter<'_, 'ctx>,
        context: &mut dyn SymInterpreterContext<'ctx>,
    ) -> VMResult<PluginError<'ctx>> {
        let first_value = ast::Int::new_const;
        let mut handle = ast::BV::bvadd_no_overflow();
    }

}

/***************************************************************************************
*
* SingleInstrPlugin Manager
*
*   Implementation of the Plugin hook trait for single line code integer check, function check
*   and transaction check.
*
**************************************************************************************/
pub struct SingleInstrPlugin<'ctx> {
    singleInstr: &'ctx Z3Context,
    solver: Z3Solver<'ctx>,
}

impl<'ctx> SingleInstrPlugin<'ctx> {
    fn new(ctx: &'ctx Z3Context) -> Self {
        SingleInstrPlugin {
            singleInstr,
            solver: Z3Solver::new(ctx),
        }
    }
    pub fn singleInstr(&self) -> &'ctx Z3Context {
        self.singleInstr
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
    pub fn PluginAddHook(
        &mut self,
        solver: &'ctx Solver<'ctx>,
        first_value: &mut Z3Context,
        context: &mut dyn SymInterpreterContext<'ctx>,
    ) -> VMResult<PluginError<'ctx>> {
        let first_value = ast::Int::new_const;
        let mut handle = ast::BV::bvadd_no_overflow();
    }
}

