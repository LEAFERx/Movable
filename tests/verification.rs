use move_core_types::identifier::{Identifier, IdentStr};
use vm::CompiledModule;
use std::{
  fs,
  path::Path,
};
use engine::Engine;

use z3::{ast::{Ast, Bool, BV}, Config, Context};
use symbolic_vm::{
  plugin::{Specification, VerificationPlugin},
  types::values::{SymBool, SymU64, SymValue, VMSymValueCast},
};


fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> Vec<u8> {
  fs::read(bytecode_path).expect("Failed to open bytecode file")
}

fn exec<'a, 'ctx>(path: &str, func: &str, z3_ctx: &'ctx Context, p: VerificationPlugin<'a, 'ctx>) {
  env_logger::init();

  let path = Path::new(path);
  let function_name = IdentStr::new(func).unwrap();
  let blob = read_bytecode(path);
  let module = CompiledModule::deserialize(blob.as_slice())
    .expect("Failed to deserialize bytecode. File may be corrupted.");

  let mut engine = Engine::from_genesis(z3_ctx);
  engine.add_module(&module.self_id(), blob);
  engine.add_plugin(p);
  engine.execute_function(&module.self_id(), &function_name);
}

struct AbsSpec<'a, 'ctx> {
  right: Specification<'a, 'ctx>,
  wrong: Specification<'a, 'ctx>,
}

#[test]
fn abs() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  let target_spec = Specification::new(
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true),
    |_a: &[SymValue], r: &[SymValue]| {
      VMSymValueCast::<SymBool>::cast(r[0].copy_value().unwrap()).unwrap()
    },
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true)
  );
  let abs_spec_wrong = Specification::new(
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true),
    |_a: &[SymValue], r: &[SymValue]| {
      // TODO: bad type conversions and clones
      // TODO: figure it out
      let ret = VMSymValueCast::<SymU64>::cast(r[0].copy_value().unwrap()).unwrap();
      SymBool::from_ast(
        ret.as_inner().bvuge(&BV::from_u64(&z3_ctx, 10, 64)),
      )
    },
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true)
  );
  let abs_spec_right = Specification::new(
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true),
    |a: &[SymValue], r: &[SymValue]| {
      // TODO: bad type conversions and clones
      // TODO: figure it out
      let arg = VMSymValueCast::<SymU64>::cast(a[0].copy_value().unwrap()).unwrap();
      let ret = VMSymValueCast::<SymU64>::cast(r[0].copy_value().unwrap()).unwrap();
      let const_ten = BV::from_u64(&z3_ctx, 10, 64);
      let arg_ast = arg.as_inner();
      let ret_ast = ret.as_inner();
      let cond_pos = arg_ast.bvuge(&const_ten).implies(&ret_ast._eq(&arg_ast));
      let cond_neg = arg_ast.bvult(&const_ten).implies(&ret_ast._eq(&const_ten.bvsub(&arg_ast)));
      let cond = Bool::and(&z3_ctx, &[&cond_pos, &cond_neg]);
      SymBool::from_ast(cond)
    },
    |_a: &[SymValue]| SymBool::from(&z3_ctx, true)
  );
  let abs_spec = AbsSpec {
    wrong: abs_spec_wrong,
    right: abs_spec_right,
  };
  let mut verification_plugin = VerificationPlugin::new(&z3_ctx, target_spec);
  let func_name = Identifier::new("abs_on_ten").unwrap();
  verification_plugin.add_spec(func_name, abs_spec.wrong);
  exec("testsuites/abs.mv", "f", &z3_ctx, verification_plugin);
}