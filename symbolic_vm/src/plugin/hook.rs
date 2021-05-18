use crate::types::{vm_context::SymbolicVMContext, values::SymValue};
use crate::{
  runtime::interpreter::SymInterpreter,
  runtime::loader::{Function, Loader, Resolver},
};
use diem_types::vm_error::{sub_status, VMStatus};
use nix::unistd::{fork, ForkResult};
use z3::Solver;
use std::{clone::Clone, marker::PhantomData, process::exit, sync::Arc};
use vm::errors::VMResult;
use vm::file_format::{CodeOffset, FunctionHandleIndex, FunctionInstantiationIndex};
use z3::ast::Dynamic;
use z3::{
  ast::Bool, ast::Int, ast::BV, Context as Z3Context, Model as Z3Model, SatResult,
  Solver as Z3Solver,
};
/***************************************************************************************
*
* Plugin Manager
*
*   Implementation of the Plugin hook trait for single line code integer check, function check
*   and transaction check.
*
**************************************************************************************/

enum PluginError {
  Return,
  Call(FunctionHandleIndex),
  CallGeneric(FunctionInstantiationIndex),
}

/***************************************************************************************
*
*  Execution Function Plugin
*
*  The user provide the pre and post condition, and it check the post will satisfy the pre condidtion
*  after the exection.
*
**************************************************************************************/

pub struct ExecutionPlugin<'ctx> {
  pre: &'ctx Z3Context,
  post: &'ctx Z3Context,
  presolver: Z3Solver<'ctx>,
  postsolver: Z3Solver<'ctx>,
}

impl<'ctx> ExecutionPlugin<'ctx> {
  fn new(pre: &'ctx Z3Context, post: &'ctx Z3Context) -> Self {
    ExecutionPlugin {
      pre,
      post,
      presolver: Z3Solver::new(pre),
      postsolver: Z3Solver::new(pre),
    }
  }
  pub fn pre(&self) -> &'ctx Z3Context {
    self.pre
  }
  pub fn post(&self) -> &'ctx Z3Context {
    self.post
  }
  pub fn assert(&self, cond: &Bool<'ctx>) {
    self.presolver.assert(cond);
  }
  pub fn check(&self) -> SatResult {
    self.presolver.check()
  }
  pub fn get_model(&self) -> Z3Model {
    self.presolver.get_model()
  }
  fn ExecutionPluginHook(
    &mut self,
    solver: &'ctx Solver,
    interpreter: &mut SymInterpreter<'_, 'ctx>,
    context: &mut dyn SymbolicVMContext<'ctx>,
  ) -> PartialVMResult<()> {
    Ok(())
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
  fn new(singleInstr: &'ctx Z3Context) -> Self {
    SingleInstrPlugin {
      singleInstr,
      solver: Z3Solver::new(singleInstr),
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
  pub fn PluginAddOverFlowHook(
    &mut self,
    solver: &'ctx Z3Solver<'ctx>,
    first_value: &mut Int,
    second_value: &mut Int,
    size_of_int: u32,
    sign_or_not: bool,
  ) -> PartialVMResult<()> {
    let mut msg = String::from("\n------------PluginAddHook------------\n");
    let x = BV::from_int(&first_value, size_of_int);
    let y = BV::from_int(&second_value, size_of_int);
    let handle = BV::bvadd_no_overflow(&x, &y, sign_or_not);
    solver.push();
    solver.assert(&handle);
    if solver.check() == SatResult::Unsat {
      msg += &format!("Add overflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    let reverse_handle = BV::bvadd_no_overflow(&x, &y, sign_or_not);
    solver.push();
    solver.assert(&reverse_handle);
    if solver.check() != SatResult::Sat {
      msg += &format!("Add overflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    msg += "-------------------------------------\n";
    print!("{}", msg);
    Ok(())
  }

  pub fn PluginAddUnderFlowHook(
    &mut self,
    solver: &'ctx Z3Solver<'ctx>,
    first_value: &mut Int,
    second_value: &mut Int,
    size_of_int: u32,
  ) -> PartialVMResult<()> {
    let mut msg = String::from("\n------------PluginAddHook------------\n");
    let x = BV::from_int(&first_value, size_of_int);
    let y = BV::from_int(&second_value, size_of_int);
    let handle = BV::bvadd_no_underflow(&x, &y);
    solver.push();
    solver.assert(&handle);
    if solver.check() == SatResult::Unsat {
      msg += &format!("Add underflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    let reverse_handle = BV::bvadd_no_underflow(&x, &y);
    solver.push();
    solver.assert(&reverse_handle);
    if solver.check() != SatResult::Sat {
      msg += &format!("Add underflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    msg += "-------------------------------------\n";
    print!("{}", msg);
    Ok(())
  }

  pub fn PluginSubOverFlowHook(
    &mut self,
    solver: &'ctx Z3Solver<'ctx>,
    first_value: &mut Int,
    second_value: &mut Int,
    size_of_int: u32,
  ) -> PartialVMResult<()> {
    let mut msg = String::from("\n------------PluginAddHook------------\n");
    let x = BV::from_int(&first_value, size_of_int);
    let y = BV::from_int(&second_value, size_of_int);
    let handle = BV::bvsub_no_overflow(&x, &y);
    solver.push();
    solver.assert(&handle);

    if solver.check() == SatResult::Unsat {
      msg += &format!("Sub overflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    let reverse_handle = BV::bvsub_no_overflow(&x, &y);
    solver.push();
    solver.assert(&reverse_handle);
    if solver.check() != SatResult::Sat {
      msg += &format!("Sub overflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    msg += "-------------------------------------\n";
    print!("{}", msg);
    Ok(())
  }
  pub fn PluginSubUnderFlowHook(
    &mut self,
    solver: &'ctx Z3Solver<'ctx>,
    first_value: &mut Int,
    second_value: &mut Int,
    size_of_int: u32,
    sign_or_not: bool,
  ) -> PartialVMResult<()> {
    let mut msg = String::from("\n------------PluginAddHook------------\n");
    let x = BV::from_int(&first_value, size_of_int);
    let y = BV::from_int(&second_value, size_of_int);

    let handle = BV::bvsub_no_underflow(&x, &y, sign_or_not);
    solver.push();
    solver.assert(&handle);

    if solver.check() == SatResult::Unsat {
      msg += &format!("Sub underflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    let reverse_handle = BV::bvsub_no_underflow(&x, &y, sign_or_not);
    solver.push();
    solver.assert(&reverse_handle);
    if solver.check() != SatResult::Sat {
      msg += &format!("Sub underflow! exit.\n");
      print!("{}", msg);
      exit(0);
    }
    solver.pop(1);
    msg += "-------------------------------------\n";
    print!("{}", msg);
    Ok(())
  }
}
