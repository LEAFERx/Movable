use move_core_types::{
  account_address::AccountAddress,
  identifier::{Identifier, IdentStr},
  language_storage::{TypeTag, StructTag},
};
use vm::CompiledModule;
use std::{
  fs,
  path::Path,
};
use engine::Engine;

use z3::{ast::{Ast, Bool, BV}, Config, Context};
use symbolic_vm::{
  plugin::*,
  runtime::{
    context::TypeContext,
  },
  types::{
    memory::SymMemory,
    values::*,
  },
};


fn read_bytecode<P: AsRef<Path>>(bytecode_path: P) -> Vec<u8> {
  fs::read(bytecode_path).expect("Failed to open bytecode file")
}

fn exec<'a, 'ctx>(path: &str, func: &str, z3_ctx: &'ctx Context, p: VerificationPlugin<'a>) {
  env_logger::init();

  let path = Path::new(path);
  let function_name = IdentStr::new(func).unwrap();
  let blob = read_bytecode(path);
  let module = CompiledModule::deserialize(blob.as_slice())
    .expect("Failed to deserialize bytecode. File may be corrupted.");

  let mut engine = Engine::from_genesis();
  engine.add_module(&module.self_id(), blob);
  engine.add_plugin(p);
  engine.execute_function(z3_ctx, &module.self_id(), &function_name);
}

struct AbsSpec<'a> {
  right: FunctionSpec<'a>,
  wrong: FunctionSpec<'a>,
}

#[test]
fn abs() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  fn target_ensures<'ctx>(_z3_ctx: &'ctx Context, _ty_ctx: &TypeContext<'ctx>, _a: &[SymValue<'ctx>], r: &[SymValue<'ctx>], _om: &SymMemory<'ctx>, _m: &SymMemory<'ctx>) -> SymBool<'ctx> {
    r[0].copy_value().unwrap().value_as::<SymBool>().unwrap()
  }
  let target_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    target_ensures.into(),
    FunctionAbortsIfSpec::default(),
    FunctionModifiesSpec::default(),
  );
  let abs_spec_wrong = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    FunctionEnsuresSpec::new(|z3_ctx: &Context, _ty_ctx: &TypeContext, _a: &[SymValue], r: &[SymValue], _om: &SymMemory, _m: &SymMemory| {
      // TODO: bad type conversions and clones
      // TODO: figure it out
      let ret = r[0].copy_value().unwrap().value_as::<SymU64>().unwrap();
      SymBool::from_ast(
        ret.as_inner().bvuge(&BV::from_u64(&z3_ctx, 10, 64)),
      )
    }),
    FunctionAbortsIfSpec::default(),
    FunctionModifiesSpec::default(),
  );
  let abs_spec_right = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    FunctionEnsuresSpec::new(|z3_ctx: &Context, _ty_ctx: &TypeContext, a: &[SymValue], r: &[SymValue], _om: &SymMemory, _m: &SymMemory| {
      // TODO: bad type conversions and clones
      // TODO: figure it out
      let arg = a[0].copy_value().unwrap().value_as::<SymU64>().unwrap();
      let ret = r[0].copy_value().unwrap().value_as::<SymU64>().unwrap();
      let const_ten = BV::from_u64(&z3_ctx, 10, 64);
      let arg_ast = arg.as_inner();
      let ret_ast = ret.as_inner();
      let cond_pos = arg_ast.bvuge(&const_ten).implies(&ret_ast._eq(&arg_ast));
      let cond_neg = arg_ast.bvult(&const_ten).implies(&ret_ast._eq(&const_ten.bvsub(&arg_ast)));
      let cond = Bool::and(&z3_ctx, &[&cond_pos, &cond_neg]);
      SymBool::from_ast(cond)
    }),
    FunctionAbortsIfSpec::default(),
    FunctionModifiesSpec::default(),
  );
  let abs_spec = AbsSpec {
    wrong: abs_spec_wrong,
    right: abs_spec_right,
  };
  let mut verification_plugin = VerificationPlugin::new(target_spec);
  let func_name = Identifier::new("abs_on_ten").unwrap();
  verification_plugin.add_spec(func_name, abs_spec.wrong);
  exec("testsuites/abs.mv", "f", &z3_ctx, verification_plugin);
}

fn signer_addr<'ctx>(ty_ctx: &TypeContext<'ctx>, signer: SymValue<'ctx>) -> SymAccountAddress<'ctx> {
  signer.value_as::<SymStructRef>().unwrap()
    .borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymAccountAddress>().unwrap()
}

fn make_struct_type(address: &str, module: &str, name: &str, type_params: Vec<TypeTag>) -> TypeTag {
  let tag = StructTag {
    address: AccountAddress::from_hex_literal(address).unwrap(),
    module: Identifier::new(module).unwrap(),
    name: Identifier::new(name).unwrap(),
    type_params: type_params,
  };
  TypeTag::Struct(tag)
}

fn exists<'ctx>(
  z3_ctx: &'ctx Context,
  ty_ctx: &TypeContext<'ctx>,
  memory: &SymMemory<'ctx>,
  addr: SymAccountAddress<'ctx>,
  ty: TypeTag,
) -> Bool<'ctx> {
  memory.load_resource(z3_ctx, ty_ctx, addr, ty).unwrap().some.0
}

fn not_exists<'ctx>(
  z3_ctx: &'ctx Context,
  ty_ctx: &TypeContext<'ctx>,
  memory: &SymMemory<'ctx>,
  addr: SymAccountAddress<'ctx>,
  ty: TypeTag,
) -> Bool<'ctx> {
  memory.load_resource(z3_ctx, ty_ctx, addr, ty).unwrap().none.0
}

fn bar2_ensures<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], _r: &[SymValue<'ctx>], _om: &SymMemory<'ctx>, m: &SymMemory<'ctx>) -> SymBool<'ctx> {
  let addr = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let ty = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  let res = m.load_resource(z3_ctx, ty_ctx, addr, ty).unwrap();

  let some = res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap()
    .borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymU64>().unwrap();
  let cond = Bool::and(z3_ctx, &[&res.some.0, &some.as_inner()._eq(&BV::from_u64(z3_ctx, 3, 64))]);

  SymBool::from_ast(cond)
}

fn bar2_aborts_if<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], om: &SymMemory<'ctx>) -> SymBool<'ctx> {
  let addr = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let ty = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  SymBool::from_ast(not_exists(z3_ctx, ty_ctx, om, addr, ty))
}

fn bar2_modifies<'ctx>(_z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], _om: &SymMemory<'ctx>) -> Vec<(SymAccountAddress<'ctx>, TypeTag)> {
  let addr = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let ty = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  vec![(addr, ty)]
}

#[test]
fn alias_bar2() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  let bar2_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar2_ensures.into(),
    bar2_aborts_if.into(),
    bar2_modifies.into(),
  );

  let verification_plugin = VerificationPlugin::new(bar2_spec);
  exec("testsuites/aliasing_move_modifies_address.mv", "bar2", &z3_ctx, verification_plugin);
}

fn bar_ensures<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], _r: &[SymValue<'ctx>], _om: &SymMemory<'ctx>, m: &SymMemory<'ctx>) -> SymBool<'ctx> {
  let account = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let ty = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  let account_u_res = m.load_resource(z3_ctx, ty_ctx, account, ty).unwrap();

  let account_u_g = account_u_res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap()
    .borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymU64>().unwrap();
  let cond = Bool::and(z3_ctx, &[
    &account_u_res.some.0,
    &Bool::or(z3_ctx, &[
      &account_u_g.as_inner()._eq(&BV::from_u64(z3_ctx, 0, 64)),
      &account_u_g.as_inner()._eq(&BV::from_u64(z3_ctx, 1, 64)),
      &account_u_g.as_inner()._eq(&BV::from_u64(z3_ctx, 2, 64)),
    ]),
  ]);

  SymBool::from_ast(cond)
}

fn bar_aborts_if<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], om: &SymMemory<'ctx>) -> SymBool<'ctx> {
  let account = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let addr1 = a[1].copy_value().unwrap().value_as::<SymAccountAddress>().unwrap();
  let addr2 = a[2].copy_value().unwrap().value_as::<SymAccountAddress>().unwrap();
  let ty_u = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  let ty_t = make_struct_type("0x123", "M", "T", vec![TypeTag::Address]);
  let ty_s = make_struct_type("0x123", "M", "S", vec![TypeTag::Address]);
  
  let addr1_t_res = om.load_resource(z3_ctx, ty_ctx, addr1, ty_t).unwrap();
  let addr1_t = addr1_t_res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap();
  let addr1_t_f = addr1_t.borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymAccountAddress>().unwrap();
  
  let addr2_s_res = om.load_resource(z3_ctx, ty_ctx, addr2, ty_s).unwrap();
  let addr2_s = addr2_s_res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap();
  let addr2_s_h = addr2_s.borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymAccountAddress>().unwrap();

  let cond = Bool::or(z3_ctx, &[
    &exists(z3_ctx, ty_ctx, om, account.clone(), ty_u.clone()),
    &addr1_t_res.none.0,
    &addr2_s_res.none.0,
    &Bool::and(z3_ctx, &[
      &not_exists(z3_ctx, ty_ctx, om, addr1_t_f.clone(), ty_u.clone()),
      &addr1_t_res.some.0,
      &addr1_t_f.as_inner()._eq(account.as_inner()).not(),
    ]),
    &Bool::and(z3_ctx, &[
      &not_exists(z3_ctx, ty_ctx, om, addr2_s_h.clone(), ty_u),
      &addr2_s_res.some.0,
      &addr2_s_h.as_inner()._eq(account.as_inner()).not(),
    ]),
  ]);
  
  SymBool::from_ast(cond)
}

fn bar_modifies<'ctx>(z3_ctx: &'ctx Context, ty_ctx: &TypeContext<'ctx>, a: &[SymValue<'ctx>], om: &SymMemory<'ctx>) -> Vec<(SymAccountAddress<'ctx>, TypeTag)> {
  let account = signer_addr(ty_ctx, a[0].copy_value().unwrap());
  let addr1 = a[1].copy_value().unwrap().value_as::<SymAccountAddress>().unwrap();
  let addr2 = a[2].copy_value().unwrap().value_as::<SymAccountAddress>().unwrap();
  let ty_u = make_struct_type("0x123", "M", "U", vec![TypeTag::U64]);
  let ty_t = make_struct_type("0x123", "M", "T", vec![TypeTag::Address]);
  let ty_s = make_struct_type("0x123", "M", "S", vec![TypeTag::Address]);
  
  let addr1_t_res = om.load_resource(z3_ctx, ty_ctx, addr1, ty_t).unwrap();
  let addr1_t = addr1_t_res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap();
  let addr1_t_f = addr1_t.borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymAccountAddress>().unwrap();
  
  let addr2_s_res = om.load_resource(z3_ctx, ty_ctx, addr2, ty_s).unwrap();
  let addr2_s = addr2_s_res.some.1.borrow_global().unwrap()
    .value_as::<SymStructRef>().unwrap();
  let addr2_s_h = addr2_s.borrow_field(ty_ctx, 0).unwrap()
    .value_as::<SymReference>().unwrap()
    .read_ref(ty_ctx).unwrap()
    .value_as::<SymAccountAddress>().unwrap();

  vec![(account, ty_u.clone()), (addr1_t_f, ty_u.clone()), (addr2_s_h, ty_u)]
}

#[test]
fn alias_bar() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  let bar_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar_ensures.into(),
    bar_aborts_if.into(),
    bar_modifies.into(),
  );

  let verification_plugin = VerificationPlugin::new(bar_spec);
  exec("testsuites/aliasing_move_modifies_address.mv", "bar", &z3_ctx, verification_plugin);
}

#[test]
fn alias_foo() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  let foo_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar2_ensures.into(),
    bar_aborts_if.into(),
    bar_modifies.into(),
  );

  let verification_plugin = VerificationPlugin::new(foo_spec);
  exec("testsuites/aliasing_move_modifies_address.mv", "foo", &z3_ctx, verification_plugin);
}

#[test]
fn alias_foo_opaque() {
  let z3_cfg = Config::new();
  let z3_ctx = Context::new(&z3_cfg);

  let foo_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar2_ensures.into(),
    bar_aborts_if.into(),
    bar_modifies.into(),
  );

  let bar_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar_ensures.into(),
    bar_aborts_if.into(),
    bar_modifies.into(),
  );

  let bar2_spec = FunctionSpec::new(
    FunctionRequiresSpec::default(),
    bar2_ensures.into(),
    bar2_aborts_if.into(),
    bar2_modifies.into(),
  );

  let mut verification_plugin = VerificationPlugin::new(foo_spec);
  verification_plugin.add_spec(Identifier::new("bar").unwrap(), bar_spec);
  verification_plugin.add_spec(Identifier::new("bar2").unwrap(), bar2_spec);
  exec("testsuites/aliasing_move_modifies_address.mv", "foo", &z3_ctx, verification_plugin);
}
