use crate::runtime::{execution_stack::ExecutionStack, value::SymValue};

use libra_types::vm_error::{StatusCode, VMStatus};
use nix::unistd::{fork, ForkResult};
use std::process::exit;
use vm::{
  errors::{vm_error, Location, VMResult},
  file_format::{Bytecode, CodeOffset, SignatureToken},
};
use vm_runtime::{
  code_cache::module_cache::VMModuleCache,
  loaded_data::function::{
    FunctionRef,
    FunctionReference,
  }
};
use z3::{ast, Context, Model, SatResult, Solver};

pub struct Executor<'ctx> {
  context: &'ctx Context,
  solver: Solver<'ctx>,
  execution_stack: ExecutionStack<'ctx>,
}

impl<'ctx> Executor<'ctx> {
  pub fn new(
    context: &'ctx Context,
    module_cache: VMModuleCache<'ctx>,
  ) -> Self {
    Executor {
      context,
      solver: Solver::new(&context),
      execution_stack: ExecutionStack::new(module_cache),
    }
  }
  
  pub fn module_cache(&self) -> &VMModuleCache<'ctx> {
      &self.execution_stack.module_cache
  }

  fn binop<F, T>(&mut self, f: F) -> VMResult<()>
  where
    T: ast::Ast<'ctx>,
    Option<T>: From<SymValue<'ctx>>,
    F: FnOnce(T, T) -> Option<SymValue<'ctx>>,
  {
    let rhs = self.execution_stack.pop_as::<T>()?;
    let lhs = self.execution_stack.pop_as::<T>()?;
    let result = f(lhs, rhs);
    if let Some(v) = result {
      self.execution_stack.push(v)?;
      Ok(())
    } else {
      Err(vm_error(
        self.execution_stack.location()?,
        StatusCode::ARITHMETIC_ERROR,
      ))
    }
  }

  pub fn execute_codeblock(
    &mut self,
    code: &[Bytecode],
    beginning_offset: CodeOffset,
  ) -> VMResult<CodeOffset> {
    let mut pc = beginning_offset;
    for instruction in &code[pc as usize..] {
      match instruction {
        Bytecode::Pop => {
          self.execution_stack.pop()?;
        }
        Bytecode::Ret => {
          self.execution_stack.pop_call()?;
          if self.execution_stack.is_call_stack_empty() {
            return Ok(0);
          } else {
            return Ok(self.execution_stack.top_frame()?.get_pc() + 1);
          }
        }
        Bytecode::BrTrue(offset) => {
          let condition = self.execution_stack.pop_as::<ast::Bool<'ctx>>()?;

          match fork() {
            Ok(ForkResult::Parent { .. }) => {
              println!("Fork parent: assume true->{:#?}", condition);
              self.solver.assert(&condition);
              if self.solver.check() == SatResult::Unsat {
                println!("Parent not satisfied, exit.");
                exit(0);
              }
              return Ok(*offset);
            }
            Ok(ForkResult::Child) => {
              println!("Fork child: assume false->{:#?}", condition);
              self.solver.assert(&condition.not());
              if self.solver.check() == SatResult::Unsat {
                println!("Child not satisfied, exit.");
                exit(0);
              }
            }
            Err(_) => {
              return Err(vm_error(
                self.execution_stack.location()?,
                StatusCode::ABORTED,
              ))
            }
          }
        }
        Bytecode::BrFalse(offset) => {
          let condition = self.execution_stack.pop_as::<ast::Bool<'ctx>>()?;

          match fork() {
            Ok(ForkResult::Parent { .. }) => {
              println!("Fork parent: assume true->{:#?}", condition);
              self.solver.assert(&condition);
              if self.solver.check() == SatResult::Unsat {
                println!("Parent not satisfied, exit.");
                exit(0);
              }
            }
            Ok(ForkResult::Child) => {
              println!("Fork child: assume false->{:#?}", condition);
              self.solver.assert(&condition.not());
              if self.solver.check() == SatResult::Unsat {
                println!("Child not satisfied, exit.");
                exit(0);
              }
              return Ok(*offset);
            }
            Err(_) => {
              return Err(vm_error(
                self.execution_stack.location()?,
                StatusCode::ABORTED,
              ))
            }
          }
        }
        Bytecode::Branch(offset) => return Ok(*offset),
        Bytecode::LdU64(int_const) => {
          self
            .execution_stack
            .push(SymValue::from_u64(self.context, *int_const))?;
        }
        Bytecode::LdTrue => {
          self
            .execution_stack
            .push(SymValue::from_bool(self.context, true))?;
        }
        Bytecode::LdFalse => {
          self
            .execution_stack
            .push(SymValue::from_bool(self.context, false))?;
        }
        Bytecode::CopyLoc(idx) => {
          let value = self.execution_stack.top_frame()?.copy_loc(*idx)?;
          self.execution_stack.push(value)?;
        }
        Bytecode::MoveLoc(idx) => {
          let value = self.execution_stack.top_frame_mut()?.move_loc(*idx)?;
          self.execution_stack.push(value)?;
        }
        Bytecode::StLoc(idx) => {
          let value = self.execution_stack.pop()?;
          self
            .execution_stack
            .top_frame_mut()?
            .store_loc(*idx, value)?;
        }
        Bytecode::Call(idx, _) => {
          let self_module = &self.execution_stack.top_frame()?.module();
          let callee_function_ref = self
            .execution_stack
            .module_cache
            .resolve_function_ref(self_module, *idx)?
            .ok_or_else(|| VMStatus::new(StatusCode::LINKER_ERROR))?;
          if callee_function_ref.is_native() {
            // support native function later
          } else {
            self.execution_stack.top_frame_mut()?.save_pc(pc);
            self.execution_stack.push_call(callee_function_ref)?;

            return Ok(0);
          }
        }
        Bytecode::Add => self.binop(|l: ast::Int<'ctx>, r| Some(l.add(&[&r]).into()))?,
        Bytecode::Sub => self.binop(|l: ast::Int<'ctx>, r| Some(l.sub(&[&r]).into()))?,
        Bytecode::Mul => self.binop(|l: ast::Int<'ctx>, r| Some(l.mul(&[&r]).into()))?,
        Bytecode::Mod => self.binop(|l: ast::Int<'ctx>, r| Some(l.rem(&r).into()))?,
        Bytecode::Div => self.binop(|l: ast::Int<'ctx>, r| Some(l.div(&r).into()))?,
        Bytecode::BitOr => self.binop(|l: ast::Int<'ctx>, r|
          Some(l.to_ast(64).bvor(&r.to_ast(64)).to_int(false).into()))?,
        Bytecode::BitAnd => self.binop(|l: ast::Int<'ctx>, r|
          Some(l.to_ast(64).bvand(&r.to_ast(64)).to_int(false).into()))?,
        Bytecode::Xor => self.binop(|l: ast::Int<'ctx>, r|
          Some(l.to_ast(64).bvxor(&r.to_ast(64)).to_int(false).into()))?,
        Bytecode::Or => self.binop(|l: ast::Bool<'ctx>, r| Some(l.or(&[&r]).into()))?,
        Bytecode::And => self.binop(|l: ast::Bool<'ctx>, r| Some(l.and(&[&r]).into()))?,
        Bytecode::Lt => self.binop(|l: ast::Int<'ctx>, r| Some(l.lt(&r).into()))?,
        Bytecode::Gt => self.binop(|l: ast::Int<'ctx>, r| Some(l.gt(&r).into()))?,
        Bytecode::Le => self.binop(|l: ast::Int<'ctx>, r| Some(l.le(&r).into()))?,
        Bytecode::Ge => self.binop(|l: ast::Int<'ctx>, r| Some(l.ge(&r).into()))?,
        Bytecode::Abort => {
          let error_code = self.execution_stack.pop_as::<ast::Int<'ctx>>()?;
          return Err(
            vm_error(self.execution_stack.location()?, StatusCode::ABORTED)
              // 0 is sucess in normal exit, so it is safe to use 0 to represent
              // the top of the stack is not an actual u64 value
              .with_sub_status(error_code.as_u64().unwrap_or(0)),
          );
        }
        Bytecode::Eq => {
          let lhs = self.execution_stack.pop()?;
          let rhs = self.execution_stack.pop()?;
          self.execution_stack.push(lhs.equals(rhs)?)?;
        }
        Bytecode::Neq => {
          let lhs = self.execution_stack.pop()?;
          let rhs = self.execution_stack.pop()?;
          self.execution_stack.push(lhs.not_equals(rhs)?)?;
        }
        Bytecode::Not => {
          let top = self.execution_stack.pop_as::<ast::Bool<'ctx>>()?;
          self.execution_stack.push(top.not().into())?;
        }
        _ => {}
      }

      pc += 1;
    }

    Ok(code.len() as CodeOffset)
  }

  pub fn execute_function(
    &mut self,
    function: FunctionRef<'ctx>,
  ) -> VMResult<(u32, Model<'ctx>, Vec<SymValue<'ctx>>)> {
    let mut total_symbols = 0;
    let return_count = function.return_count();

    for arg_types in function.signature().arg_types.iter() {
      total_symbols += 1;
      if let Some(v) = match arg_types {
        SignatureToken::U64 => Some(SymValue::new_u64(self.context, "symbol_int")),
        SignatureToken::Bool => Some(SymValue::new_bool(self.context, "symbol_bool")),
        _ => None,
      } {
        self.execution_stack.push(v)?;
      }
    }
    let beginning_height = self.execution_stack.call_stack_height();
    self.execution_stack.push_call(function)?;
    let mut pc = 0;
    while self.execution_stack.call_stack_height() != beginning_height {
      let code = self.execution_stack.top_frame()?.code_definition();
      pc = self.execute_codeblock(code, pc)?;
    }

    let mut return_values = vec![];

    for _ in 0..return_count {
      return_values.push(self.execution_stack.pop()?);
    }

    Ok((total_symbols, self.solver.get_model(), return_values))
  }
}
