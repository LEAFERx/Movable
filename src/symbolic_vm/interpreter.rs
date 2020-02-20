use libra_logger::prelude::*;
use libra_types::{
  identifier::IdentStr,
  language_storage::{ModuleId, StructTag, TypeTag},
  vm_error::{StatusCode, StatusType, VMStatus},
};
use vm::{
  access::ModuleAccess,
  errors::*,
  file_format::{
    Bytecode, CodeOffset, FunctionHandleIndex, LocalIndex, LocalsSignatureIndex, SignatureToken,
  },
};
use vm_runtime::{
  execution_context::InterpreterContext,
  loaded_data::{
    function::{FunctionRef, FunctionReference},
    loaded_module::LoadedModule,
  },
};
use vm_runtime_types::{
  loaded_data::{types::Type},
  type_context::TypeContext,
};

use z3::{SatResult};

use nix::unistd::{fork, ForkResult};

use std::{
  fmt::Debug,
  marker::PhantomData,
  process::exit,
};

use crate::{
  engine::solver::Solver,
  symbolic_vm::{
    runtime::SymVMRuntime,
    types::{
      primitives::{SymBool, SymU8, SymU64},
      value::{
        SymIntegerValue,
        SymLocals,
        SymReference,
        SymStruct,
        SymStructRef,
        SymValue,
        VMSymValueCast,
      },
    },
  },
};

fn derive_type_tag(
  module: &impl ModuleAccess,
  type_actual_tags: &[TypeTag],
  ty: &SignatureToken,
) -> VMResult<TypeTag> {
  use SignatureToken::*;

  match ty {
      Bool => Ok(TypeTag::Bool),
      Address => Ok(TypeTag::Address),
      U8 => Ok(TypeTag::U8),
      U64 => Ok(TypeTag::U64),
      U128 => Ok(TypeTag::U128),
      ByteArray => Ok(TypeTag::ByteArray),
      TypeParameter(idx) => type_actual_tags
          .get(*idx as usize)
          .ok_or_else(|| {
              VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION).with_message(
                  "Cannot derive type tag: type parameter index out of bounds.".to_string(),
              )
          })
          .map(|inner| inner.clone()),
      Reference(_) | MutableReference(_) => {
          Err(VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION)
              .with_message("Cannot derive type tag for references.".to_string()))
      }
      Struct(idx, struct_type_actuals) => {
          let struct_type_actuals_tags = struct_type_actuals
              .iter()
              .map(|ty| derive_type_tag(module, type_actual_tags, ty))
              .collect::<VMResult<Vec<_>>>()?;
          let struct_handle = module.struct_handle_at(*idx);
          let struct_name = module.identifier_at(struct_handle.name);
          let module_handle = module.module_handle_at(struct_handle.module);
          let module_address = module.address_at(module_handle.address);
          let module_name = module.identifier_at(module_handle.name);
          Ok(TypeTag::Struct(StructTag {
              address: *module_address,
              module: module_name.into(),
              name: struct_name.into(),
              type_params: struct_type_actuals_tags,
          }))
      }
  }
}

pub struct SymInterpreter<'vtxn, 'ctx> {
  operand_stack: SymStack<'ctx>,
  call_stack: CallStack<'vtxn, 'ctx>,
}

impl<'vtxn, 'ctx> SymInterpreter<'vtxn, 'ctx> {
  pub fn execute_function(
    solver: &'ctx Solver<'ctx>,
    interp_context: &mut dyn InterpreterContext,
    runtime: &'vtxn SymVMRuntime<'ctx, '_>,
    module: &ModuleId,
    function_name: &IdentStr,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let mut interp = Self::new();
    let loaded_module = runtime.get_loaded_module(module, interp_context)?;
    let func_idx = loaded_module
      .function_defs_table
      .get(function_name)
      .ok_or_else(|| VMStatus::new(StatusCode::LINKER_ERROR))?;
    let func = FunctionRef::new(loaded_module, *func_idx);

    interp.execute_main(solver, runtime, interp_context, func, args)
  }

  fn new() -> Self {
    SymInterpreter {
      operand_stack: SymStack::new(),
      call_stack: CallStack::new(),
    }
  }

  fn execute_main(
    &mut self,
    solver: &'ctx Solver<'ctx>,
    runtime: &'vtxn SymVMRuntime<'ctx, '_>,
    interp_context: &mut dyn InterpreterContext,
    function: FunctionRef<'vtxn>,
    args: Vec<SymValue<'ctx>>,
  ) -> VMResult<()> {
    let mut msg = String::from("\n-------------------------\n");

    let mut locals = SymLocals::new(solver, function.local_count());
    for (i, value) in args.iter().enumerate() {
      locals.store_loc(i, value.copy_value())?;
    }
    let mut current_frame = Frame::new(function, vec![], vec![], locals);
    loop {
      let code = current_frame.code_definition();
      let exit_code = self
        .execute_code_unit(solver, runtime, interp_context, &mut current_frame, code)
        .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
      match exit_code {
        ExitCode::Return => {
          if let Some(frame) = self.call_stack.pop() {
            current_frame = frame;
          } else {
            // Assume now function is fully executed
            break;
            // return Err(self.unreachable("call stack cannot be empty", &current_frame));
          }
        }
        ExitCode::Call(idx, type_actuals_idx) => {
          let type_actuals_sig = &current_frame
            .module()
            .locals_signature_at(type_actuals_idx)
            .0;
          // gas!(
          //   instr: context,
          //   self,
          //   Opcodes::CALL,
          //   AbstractMemorySize::new((type_actuals_sig.len() + 1) as GasCarrier)
          // )?;
          let type_actual_tags = type_actuals_sig
            .iter()
            .map(|ty| derive_type_tag(current_frame.module(), current_frame.type_actual_tags(), ty))
            .collect::<VMResult<Vec<_>>>()?;
          let type_context = TypeContext::new(current_frame.type_actuals().to_vec());
          let type_actuals = type_actuals_sig
            .iter()
            .map(|ty| {
              runtime.resolve_signature_token(current_frame.module(), ty, &type_context, interp_context)
            })
            .collect::<VMResult<Vec<_>>>()?;

          let opt_frame = self
            .make_call_frame(
              solver,
              runtime,
              interp_context,
              current_frame.module(),
              idx,
              type_actual_tags,
              type_actuals,
            )
            .or_else(|err| Err(self.maybe_core_dump(err, &current_frame)))?;
          if let Some(frame) = opt_frame {
            self.call_stack.push(current_frame).or_else(|frame| {
              let err = VMStatus::new(StatusCode::CALL_STACK_OVERFLOW);
              Err(self.maybe_core_dump(err, &frame))
            })?;
            current_frame = frame;
          }
        }
        ExitCode::Branch(instr, condition, offset) => {
          println!(
            "Hit Br{{{:?}}} instr, condition is {:?}, target offset is {:?}",
            instr,
            condition,
            offset,
          );
          // Temp use fork to explore all branch
          // Use task stack to implement DFS later
          match fork() {
            Ok(ForkResult::Parent { .. }) => {
              msg += &format!("Fork parent: assume {:?}->{:#?}\n", instr, condition);
              if instr {
                solver.assert(&condition.as_inner());
              } else {
                solver.assert(&condition.not().as_inner());
              }
              if solver.check() == SatResult::Unsat {
                msg += &format!("Parent not satisfied, exit.\n");
                exit(0);
              }
              current_frame.pc = offset;
            }
            Ok(ForkResult::Child) => {
              msg += &format!("Fork child: assume {:?}->{:#?}\n", !instr, condition);
              if instr {
                solver.assert(&condition.not().as_inner());
              } else {
                solver.assert(&condition.as_inner());
              }
              if solver.check() == SatResult::Unsat {
                msg += &format!("Child not satisfied, exit.\n");
                exit(0);
              }
            }
            Err(_) => {
              return Err(VMStatus::new(StatusCode::ABORTED).with_message("Unable to fork, abort.".to_string()));
            }
          }
        }
      }
    }

    let model = solver.get_model();
    msg += "Test Function Arguments\n";
    for (i, v) in args.into_iter().enumerate() {
      msg += &format!("  {}: {:#?}\n", i, model.eval(&v.into_ast()?));
    }
    msg += "Test Function Returns\n";
    for i in 0..current_frame.function.return_count() {
      msg += &format!("  {}: {:#?}\n", i, model.eval(&self.operand_stack.pop()?.into_ast()?));
    }
    msg += &format!("-------------------------\n");
    print!("{}", msg);
    Ok(())
  }

  fn execute_code_unit(
    &mut self,
    solver: &'ctx Solver<'ctx>,
    _runtime: &'vtxn SymVMRuntime<'ctx, '_>,
    _interp_context: &mut dyn InterpreterContext,
    frame: &mut Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>,
    code: &[Bytecode],
  ) -> VMResult<ExitCode<'ctx>> {
    loop {
      for instruction in &code[frame.pc as usize..] {
        frame.pc += 1;

        match instruction {
          Bytecode::Pop => {
            // gas!(const_instr: context, self, Opcodes::POP)?;
            self.operand_stack.pop()?;
          }
          Bytecode::Ret => {
            // gas!(const_instr: context, self, Opcodes::RET)?;
            return Ok(ExitCode::Return);
          }
          Bytecode::BrTrue(offset) => {
            return Ok(ExitCode::Branch(true, self.operand_stack.pop_as::<SymBool>()?, *offset));
            // gas!(const_instr: context, self, Opcodes::BR_TRUE)?;
            // if self.operand_stack.pop_as::<bool>()? {
            //   frame.pc = *offset;
            //   break;
            // }
          }
          Bytecode::BrFalse(offset) => {
            return Ok(ExitCode::Branch(false, self.operand_stack.pop_as::<SymBool>()?, *offset));
            // gas!(const_instr: context, self, Opcodes::BR_FALSE)?;
            // if !self.operand_stack.pop_as::<bool>()? {
            //   frame.pc = *offset;
            //   break;
            // }
          }
          Bytecode::Branch(offset) => {
            // gas!(const_instr: context, self, Opcodes::BRANCH)?;
            frame.pc = *offset;
            break;
          }
          Bytecode::LdU8(int_const) => {
            // gas!(const_instr: context, self, Opcodes::LD_U8)?;
            self
              .operand_stack
              .push(SymValue::from_u8(solver, *int_const))?;
          }
          Bytecode::LdU64(int_const) => {
            // gas!(const_instr: context, self, Opcodes::LD_U64)?;
            self
              .operand_stack
              .push(SymValue::from_u64(solver, *int_const))?;
          }
          Bytecode::LdU128(int_const) => {
            // gas!(const_instr: context, self, Opcodes::LD_U128)?;
            self
              .operand_stack
              .push(SymValue::from_u128(solver, *int_const))?;
          }
          Bytecode::LdAddr(idx) => {
            // gas!(const_instr: context, self, Opcodes::LD_ADDR)?;
            self.operand_stack.push(SymValue::from_address(
              solver,
              *frame.module().address_at(*idx),
            ))?;
          }
          Bytecode::LdByteArray(idx) => {
            let byte_array = frame.module().byte_array_at(*idx);
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::LD_BYTEARRAY,
            //   AbstractMemorySize::new(byte_array.len() as GasCarrier)
            // )?;
            self
              .operand_stack
              .push(SymValue::from_byte_array(solver, byte_array.clone()))?;
          }
          Bytecode::LdTrue => {
            // gas!(const_instr: context, self, Opcodes::LD_TRUE)?;
            self.operand_stack.push(SymValue::from_bool(solver, true))?;
          }
          Bytecode::LdFalse => {
            // gas!(const_instr: context, self, Opcodes::LD_TRUE)?;
            self.operand_stack.push(SymValue::from_bool(solver, false))?;
          }
          Bytecode::CopyLoc(idx) => {
            let local = frame.copy_loc(*idx)?;
            // gas!(instr: context, self, Opcodes::COPY_LOC, local.size())?;
            self.operand_stack.push(local)?;
          }
          Bytecode::MoveLoc(idx) => {
            let local = frame.move_loc(*idx)?;
            // gas!(instr: context, self, Opcodes::MOVE_LOC, local.size())?;
            self.operand_stack.push(local)?;
          }
          Bytecode::StLoc(idx) => {
            let value_to_store = self.operand_stack.pop()?;
            // gas!(instr: context, self, Opcodes::ST_LOC, value_to_store.size())?;
            frame.store_loc(*idx, value_to_store)?;
          }
          Bytecode::Call(idx, type_actuals_idx) => {
            return Ok(ExitCode::Call(*idx, *type_actuals_idx));
          }
          Bytecode::MutBorrowLoc(idx) | Bytecode::ImmBorrowLoc(idx) => {
            // let opcode = match instruction {
            //   Bytecode::MutBorrowLoc(_) => Opcodes::MUT_BORROW_LOC,
            //   _ => Opcodes::IMM_BORROW_LOC,
            // };
            // gas!(const_instr: context, self, opcode)?;
            self.operand_stack.push(frame.borrow_loc(*idx)?)?;
          }
          Bytecode::ImmBorrowField(fd_idx) | Bytecode::MutBorrowField(fd_idx) => {
            // let opcode = match instruction {
            //   Bytecode::MutBorrowField(_) => Opcodes::MUT_BORROW_FIELD,
            //   _ => Opcodes::IMM_BORROW_FIELD,
            // };
            // gas!(const_instr: context, self, opcode)?;
            let field_offset = frame.module().get_field_offset(*fd_idx)?;
            let reference = self.operand_stack.pop_as::<SymStructRef>()?;
            let field_ref = reference.borrow_field(field_offset as usize)?;
            self.operand_stack.push(field_ref)?;
          }
          Bytecode::Pack(sd_idx, _) => {
            let struct_def = frame.module().struct_def_at(*sd_idx);
            let field_count = struct_def.declared_field_count()?;
            let args = self.operand_stack.popn(field_count)?;
            // let size = args.iter().fold(
            //   AbstractMemorySize::new(GasCarrier::from(field_count)),
            //   |acc, arg| acc.add(arg.size()),
            // );
            // gas!(instr: context, self, Opcodes::PACK, size)?;
            self.operand_stack
              .push(SymValue::from_sym_struct(SymStruct::pack(solver, args)))?;
          }
          Bytecode::Unpack(_sd_idx, _) => {
            // let struct_def = frame.module().struct_def_at(*sd_idx);
            // let field_count = struct_def.declared_field_count()?;
            let struct_ = self.operand_stack.pop_as::<SymStruct>()?;
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::UNPACK,
            //   AbstractMemorySize::new(GasCarrier::from(field_count))
            // )?;
            // TODO: Whether or not we want this gas metering in the loop is
            // questionable.  However, if we don't have it in the loop we could wind up
            // doing a fair bit of work before charging for it.
            for value in struct_.unpack()? {
              // gas!(instr: context, self, Opcodes::UNPACK, value.size())?;
              self.operand_stack.push(value)?;
            }
          }
          Bytecode::ReadRef => {
            let reference = self.operand_stack.pop_as::<SymReference>()?;
            let value = reference.read_ref()?;
            // gas!(instr: context, self, Opcodes::READ_REF, value.size())?;
            self.operand_stack.push(value)?;
          }
          Bytecode::WriteRef => {
            let reference = self.operand_stack.pop_as::<SymReference>()?;
            let value = self.operand_stack.pop()?;
            // gas!(instr: context, self, Opcodes::WRITE_REF, value.size())?;
            reference.write_ref(value)?;
          }
          Bytecode::CastU8 => {
            // gas!(const_instr: context, self, Opcodes::CAST_U8)?;
            let integer_value = self.operand_stack.pop_as::<SymIntegerValue>()?;
            self.operand_stack.push(SymValue::from_sym_u8(integer_value.cast_u8()))?;
          }
          Bytecode::CastU64 => {
            // gas!(const_instr: context, self, Opcodes::CAST_U64)?;
            let integer_value = self.operand_stack.pop_as::<SymIntegerValue>()?;
            self.operand_stack.push(SymValue::from_sym_u64(integer_value.cast_u64()))?;
          }
          Bytecode::CastU128 => {
            // gas!(const_instr: context, self, Opcodes::CAST_U128)?;
            let integer_value = self.operand_stack.pop_as::<SymIntegerValue>()?;
            self.operand_stack.push(SymValue::from_sym_u128(integer_value.cast_u128()))?;
          }
          // Arithmetic Operations
          Bytecode::Add => {
            // gas!(const_instr: context, self, Opcodes::ADD)?;
            self.binop_int(SymIntegerValue::add)?
          }
          Bytecode::Sub => {
            // gas!(const_instr: context, self, Opcodes::SUB)?;
            self.binop_int(SymIntegerValue::sub)?
          }
          Bytecode::Mul => {
            // gas!(const_instr: context, self, Opcodes::MUL)?;
            self.binop_int(SymIntegerValue::mul)?
          }
          Bytecode::Mod => {
            // gas!(const_instr: context, self, Opcodes::MOD)?;
            self.binop_int(SymIntegerValue::rem)?
          }
          Bytecode::Div => {
            // gas!(const_instr: context, self, Opcodes::DIV)?;
            self.binop_int(SymIntegerValue::div)?
          }
          Bytecode::BitOr => {
            // gas!(const_instr: context, self, Opcodes::BIT_OR)?;
            self.binop_int(SymIntegerValue::bit_or)?
          }
          Bytecode::BitAnd => {
            // gas!(const_instr: context, self, Opcodes::BIT_AND)?;
            self.binop_int(SymIntegerValue::bit_and)?
          }
          Bytecode::Xor => {
            // gas!(const_instr: context, self, Opcodes::XOR)?;
            self.binop_int(SymIntegerValue::bit_xor)?
          }
          Bytecode::Shl => {
            // gas!(const_instr: context, self, Opcodes::SHL)?;
            let rhs = self.operand_stack.pop_as::<SymU8>()?;
            let lhs = self.operand_stack.pop_as::<SymIntegerValue>()?;
            self
              .operand_stack
              .push(lhs.shl(rhs)?.into_value())?;
          }
          Bytecode::Shr => {
            // gas!(const_instr: context, self, Opcodes::SHR)?;
            let rhs = self.operand_stack.pop_as::<SymU8>()?;
            let lhs = self.operand_stack.pop_as::<SymIntegerValue>()?;
            self
              .operand_stack
              .push(lhs.shr(rhs)?.into_value())?;
          }
          Bytecode::Or => {
            // gas!(const_instr: context, self, Opcodes::OR)?;
            self.binop_bool(|l: SymBool<'ctx>, r| Ok(l.or(&r)))?
          }
          Bytecode::And => {
            // gas!(const_instr: context, self, Opcodes::AND)?;
            self.binop_bool(|l: SymBool<'ctx>, r| Ok(l.and(&r)))?
          }
          Bytecode::Lt => {
            // gas!(const_instr: context, self, Opcodes::LT)?;
            self.binop_bool(SymIntegerValue::lt)?
          }
          Bytecode::Gt => {
            // gas!(const_instr: context, self, Opcodes::GT)?;
            self.binop_bool(SymIntegerValue::le)?
          }
          Bytecode::Le => {
            // gas!(const_instr: context, self, Opcodes::LE)?;
            self.binop_bool(SymIntegerValue::gt)?
          }
          Bytecode::Ge => {
            // gas!(const_instr: context, self, Opcodes::GE)?;
            self.binop_bool(SymIntegerValue::ge)?
          }
          Bytecode::Abort => {
            // gas!(const_instr: context, self, Opcodes::ABORT)?;
            let sym_error_code = self.operand_stack.pop_as::<SymU64>()?;
            let error_code = sym_error_code.as_inner().as_u64();
            return match error_code {
              Some(code) => Err(VMStatus::new(StatusCode::ABORTED).with_sub_status(code)),
              None => {
                let msg = format!("With Symbolic Error Code {:?}", error_code);
                Err(VMStatus::new(StatusCode::ABORTED).with_message(msg))
              }
            }
          }
          Bytecode::Eq => {
            let lhs = self.operand_stack.pop()?;
            let rhs = self.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::EQ,
            //   lhs.size().add(rhs.size())
            // )?;
            self.operand_stack.push(SymValue::from_sym_bool(lhs.equals(&rhs)?))?;
          }
          Bytecode::Neq => {
            let lhs = self.operand_stack.pop()?;
            let rhs = self.operand_stack.pop()?;
            // gas!(
            //   instr: context,
            //   self,
            //   Opcodes::NEQ,
            //   lhs.size().add(rhs.size())
            // )?;
            self.operand_stack
              .push(SymValue::from_sym_bool(
                lhs.equals(&rhs).and_then(|res| Ok(res.not()))?
              ))?;
          }
          // Bytecode::GetTxnSenderAddress => {
          //   // gas!(const_instr: context, self, Opcodes::GET_TXN_SENDER)?;
          //   self
          //     .operand_stack
          //     .push(SymValue::address(self.txn_data.sender()))?;
          // }
          // Bytecode::MutBorrowGlobal(idx, type_actuals_idx)
          // | Bytecode::ImmBorrowGlobal(idx, type_actuals_idx) => {
          //   let addr = self.operand_stack.pop_as::<AccountAddress>()?;
          //   let size = self.global_data_op(
          //     runtime,
          //     context,
          //     addr,
          //     *idx,
          //     *type_actuals_idx,
          //     frame,
          //     Self::borrow_global,
          //   )?;
          //   // gas!(instr: context, self, Opcodes::MUT_BORROW_GLOBAL, size)?;
          // }
          // Bytecode::Exists(idx, type_actuals_idx) => {
          //   let addr = self.operand_stack.pop_as::<AccountAddress>()?;
          //   let size = self.global_data_op(
          //     runtime,
          //     context,
          //     addr,
          //     *idx,
          //     *type_actuals_idx,
          //     frame,
          //     Self::exists,
          //   )?;
          //   // gas!(instr: context, self, Opcodes::EXISTS, size)?;
          // }
          // Bytecode::MoveFrom(idx, type_actuals_idx) => {
          //   let addr = self.operand_stack.pop_as::<AccountAddress>()?;
          //   let size = self.global_data_op(
          //     runtime,
          //     context,
          //     addr,
          //     *idx,
          //     *type_actuals_idx,
          //     frame,
          //     Self::move_from,
          //   )?;
          //   // TODO: Have this calculate before pulling in the data based upon
          //   // the size of the data that we are about to read in.
          //   // gas!(instr: context, self, Opcodes::MOVE_FROM, size)?;
          // }
          // Bytecode::MoveToSender(idx, type_actuals_idx) => {
          //   let addr = self.txn_data.sender();
          //   let size = self.global_data_op(
          //     runtime,
          //     context,
          //     addr,
          //     *idx,
          //     *type_actuals_idx,
          //     frame,
          //     Self::move_to_sender,
          //   )?;
          //   // gas!(instr: context, self, Opcodes::MOVE_TO, size)?;
          // }
          // Bytecode::FreezeRef => {
          //   // FreezeRef should just be a null op as we don't distinguish between mut
          //   // and immut ref at runtime.
          // }
          Bytecode::Not => {
            // gas!(const_instr: context, self, Opcodes::NOT)?;
            let value = self.operand_stack.pop_as::<SymBool>()?.not();
            self.operand_stack.push(SymValue::from_sym_bool(value))?;
          }
          Bytecode::GetGasRemaining
          | Bytecode::GetTxnPublicKey
          | Bytecode::GetTxnSequenceNumber
          | Bytecode::GetTxnMaxGasUnits
          | Bytecode::GetTxnGasUnitPrice => {
            return Err(
              VMStatus::new(StatusCode::VERIFIER_INVARIANT_VIOLATION)
                .with_message("This opcode is deprecated and will be removed soon".to_string()),
            );
          }

          _ => {
            unimplemented!();
          }
        }
      }
      // ok we are out, it's a branch, check the pc for good luck
      // TODO: re-work the logic here. Cost synthesis and tests should have a more
      // natural way to plug in
      if frame.pc as usize >= code.len() {
        if cfg!(test) || cfg!(feature = "instruction_synthesis") {
          // In order to test the behavior of an instruction stream, hitting end of the
          // code should report no error so that we can check the
          // locals.
          return Ok(ExitCode::Return);
        } else {
          return Err(VMStatus::new(StatusCode::PC_OVERFLOW));
        }
      }
    }
  }

  fn make_call_frame(
    &mut self,
    solver: &'ctx Solver<'ctx>,
    runtime: &'vtxn SymVMRuntime<'ctx, '_>,
    interp_context: &mut dyn InterpreterContext,
    module: &LoadedModule,
    idx: FunctionHandleIndex,
    type_actual_tags: Vec<TypeTag>,
    type_actuals: Vec<Type>,
  ) -> VMResult<Option<Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>>> {
    let func = runtime.resolve_function_ref(module, idx, interp_context)?;
    if func.is_native() {
      unimplemented!();
      // self.call_native(runtime, interp_context, func, type_actual_tags)?;
      // Ok(None)
    } else {
      let mut locals = SymLocals::new(solver, func.local_count());
      let arg_count = func.arg_count();
      for i in 0..arg_count {
        locals.store_loc(arg_count - i - 1, self.operand_stack.pop()?)?;
      }
      Ok(Some(Frame::new(
        func,
        type_actual_tags,
        type_actuals,
        locals,
      )))
    }
  }

  fn binop<F, T>(&mut self, f: F) -> VMResult<()>
  where
    T: Debug,
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> VMResult<SymValue<'ctx>>,
  {
    let rhs = self.operand_stack.pop_as::<T>()?;
    let lhs = self.operand_stack.pop_as::<T>()?;
    let result = f(lhs, rhs)?;
    self.operand_stack.push(result)
  }

  /// Perform a binary operation for integer values.
  fn binop_int<F>(&mut self, f: F) -> VMResult<()>
  where
    F: FnOnce(SymIntegerValue<'ctx>, SymIntegerValue<'ctx>) -> VMResult<SymIntegerValue<'ctx>>,
  {
    self.binop(|lhs, rhs| {
      Ok(match f(lhs, rhs)? {
        SymIntegerValue::U8(x) => SymValue::from_sym_u8(x),
        SymIntegerValue::U64(x) => SymValue::from_sym_u64(x),
        SymIntegerValue::U128(x) => SymValue::from_sym_u128(x),
      })
    })
  }

  /// Perform a binary operation for boolean values.
  fn binop_bool<F, T>(&mut self, f: F) -> VMResult<()>
  where
    T: Debug,
    SymValue<'ctx>: VMSymValueCast<T>,
    F: FnOnce(T, T) -> VMResult<SymBool<'ctx>>,
  {
    self.binop(|lhs, rhs| Ok(SymValue::from_sym_bool(f(lhs, rhs)?)))
  }

  //
  // Debugging and logging helpers.
  //

  /// Given an `VMStatus` generate a core dump if the error is an `InvariantViolation`.
  fn maybe_core_dump(
    &self,
    mut err: VMStatus,
    current_frame: &Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>,
  ) -> VMStatus {
    // a verification error cannot happen at runtime so change it into an invariant violation.
    if err.status_type() == StatusType::Verification {
      crit!("Verification error during runtime: {:?}", err);
      let mut new_err = VMStatus::new(StatusCode::VERIFICATION_ERROR);
      new_err.message = err.message;
      err = new_err;
    }
    if err.is(StatusType::InvariantViolation) {
      let state = self.get_internal_state(current_frame);
      crit!(
        "Error: {:?}\nCORE DUMP: >>>>>>>>>>>>\n{}\n<<<<<<<<<<<<\n",
        err,
        state,
      );
    }
    err
  }

  /// Generate a string which is the status of the interpreter: call stack, current bytecode
  /// stream, locals and operand stack.
  ///
  /// It is used when generating a core dump but can be used for debugging of the interpreter.
  /// It will be exposed via a debug module to give developers a way to print the internals
  /// of an execution.
  fn get_internal_state(
    &self,
    current_frame: &Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>
  ) -> String {
    let mut internal_state = "Call stack:\n".to_string();
    for (i, frame) in self.call_stack.0.iter().enumerate() {
      internal_state.push_str(
        format!(
          " frame #{}: {} [pc = {}]\n",
          i,
          frame.function.pretty_string(),
          frame.pc,
        )
        .as_str(),
      );
    }
    internal_state.push_str(
      format!(
        "*frame #{}: {} [pc = {}]:\n",
        self.call_stack.0.len(),
        current_frame.function.pretty_string(),
        current_frame.pc,
      )
      .as_str(),
    );
    let code = current_frame.code_definition();
    let pc = current_frame.pc as usize;
    if pc < code.len() {
      let mut i = 0;
      for bytecode in &code[0..pc] {
        internal_state.push_str(format!("{}> {:?}\n", i, bytecode).as_str());
        i += 1;
      }
      internal_state.push_str(format!("{}* {:?}\n", i, code[pc]).as_str());
    }
    // internal_state.push_str(format!("Locals:\n{}", current_frame.locals.pretty_string()).as_str());
    internal_state.push_str(format!("Locals:\n{:?}", current_frame.locals).as_str());
    internal_state.push_str("Operand Stack:\n");
    for value in &self.operand_stack.0 {
      // internal_state.push_str(format!("{}\n", value.pretty_string()).as_str());
      internal_state.push_str(format!("{:?}\n", value).as_str());
    }
    internal_state
  }

  #[allow(dead_code)]
  /// Generate a core dump and an `UNREACHABLE` invariant violation.
  fn unreachable(
    &self,
    msg: &str,
    current_frame: &Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>
  ) -> VMStatus {
    let err = VMStatus::new(StatusCode::UNREACHABLE).with_message(msg.to_string());
    self.maybe_core_dump(err, current_frame)
  }
}

const OPERAND_STACK_SIZE_LIMIT: usize = 1024;
const CALL_STACK_SIZE_LIMIT: usize = 1024;

#[derive(Debug)]
struct SymStack<'ctx>(Vec<SymValue<'ctx>>);

impl<'ctx> SymStack<'ctx> {
  /// Create a new empty operand stack.
  fn new() -> Self {
    SymStack(vec![])
  }

  /// Push a `Value` on the stack if the max stack size has not been reached. Abort execution
  /// otherwise.
  fn push(&mut self, value: SymValue<'ctx>) -> VMResult<()> {
    if self.0.len() < OPERAND_STACK_SIZE_LIMIT {
      self.0.push(value);
      Ok(())
    } else {
      Err(VMStatus::new(StatusCode::EXECUTION_STACK_OVERFLOW))
    }
  }

  /// Pop a `Value` off the stack or abort execution if the stack is empty.
  fn pop(&mut self) -> VMResult<SymValue<'ctx>> {
    self
      .0
      .pop()
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))
  }

  /// Pop a `Value` of a given type off the stack. Abort if the value is not of the given
  /// type or if the stack is empty.
  fn pop_as<T>(&mut self) -> VMResult<T>
  where
    SymValue<'ctx>: VMSymValueCast<T>,
  {
    self.pop()?.value_as()
  }

  /// Pop n values off the stack.
  fn popn(&mut self, n: u16) -> VMResult<Vec<SymValue<'ctx>>> {
    let remaining_stack_size = self
      .0
      .len()
      .checked_sub(n as usize)
      .ok_or_else(|| VMStatus::new(StatusCode::EMPTY_VALUE_STACK))?;
    let args = self.0.split_off(remaining_stack_size);
    Ok(args)
  }
}

#[derive(Debug)]
struct CallStack<'vtxn, 'ctx>(Vec<Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>>);

impl<'vtxn, 'ctx> CallStack<'vtxn, 'ctx> {
  /// Create a new empty call stack.
  fn new() -> Self {
    CallStack(vec![])
  }

  /// Push a `Frame` on the call stack.
  fn push(
    &mut self,
    frame: Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>,
  ) -> ::std::result::Result<(), Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>> {
    if self.0.len() < CALL_STACK_SIZE_LIMIT {
      self.0.push(frame);
      Ok(())
    } else {
      Err(frame)
    }
  }

  /// Pop a `Frame` off the call stack.
  fn pop(&mut self) -> Option<Frame<'vtxn, 'ctx, FunctionRef<'vtxn>>> {
    self.0.pop()
  }
}

#[derive(Debug)]
struct Frame<'vtxn, 'ctx, F: 'vtxn> {
  pc: u16,
  locals: SymLocals<'ctx>,
  function: F,
  type_actual_tags: Vec<TypeTag>,
  type_actuals: Vec<Type>,
  phantom: PhantomData<&'vtxn F>,
}

#[derive(Debug)]
enum ExitCode<'ctx> {
  /// A `Return` opcode was found.
  Return,
  /// A `Call` opcode was found.
  Call(FunctionHandleIndex, LocalsSignatureIndex),
  /// A `BrTrue / BrFalse` opcode was found.
  /// BrTrue / BrFalse, condition , offset
  Branch(bool, SymBool<'ctx>, CodeOffset),
}

impl<'vtxn, 'ctx, F> Frame<'vtxn, 'ctx, F>
where
  F: FunctionReference<'vtxn>,
{
  /// Create a new `Frame` given a `FunctionReference` and the function `Locals`.
  ///
  /// The locals must be loaded before calling this.
  fn new(
    function: F,
    type_actual_tags: Vec<TypeTag>,
    type_actuals: Vec<Type>,
    locals: SymLocals<'ctx>,
  ) -> Self {
    Frame {
      pc: 0,
      locals,
      function,
      type_actual_tags,
      type_actuals,
      phantom: PhantomData,
    }
  }

  /// Return the code stream of this function.
  fn code_definition(&self) -> &'vtxn [Bytecode] {
    self.function.code_definition()
  }

  /// Return the `LoadedModule` this function lives in.
  fn module(&self) -> &'vtxn LoadedModule {
    self.function.module()
  }

  /// Copy a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn copy_loc(&self, idx: LocalIndex) -> VMResult<SymValue<'ctx>> {
    self.locals.copy_loc(idx as usize)
  }

  /// Move a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn move_loc(&mut self, idx: LocalIndex) -> VMResult<SymValue<'ctx>> {
    self.locals.move_loc(idx as usize)
  }

  /// Store a `Value` into a local at the given index. Return an error if the index is
  /// out of bounds.
  fn store_loc(&mut self, idx: LocalIndex, value: SymValue<'ctx>) -> VMResult<()> {
    self.locals.store_loc(idx as usize, value)
  }

  #[allow(dead_code)]
  /// Borrow a local from this frame at the given index. Return an error if the index is
  /// out of bounds or the local is `Invalid`.
  fn borrow_loc(&mut self, idx: LocalIndex) -> VMResult<SymValue<'ctx>> {
    self.locals.borrow_loc(idx as usize)
  }

  fn type_actual_tags(&self) -> &[TypeTag] {
    &self.type_actual_tags
  }

  fn type_actuals(&self) -> &[Type] {
    &self.type_actuals
  }
}
