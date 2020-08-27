use libra_types::{
  vm_error::{
    sub_status::NFE_VECTOR_ERROR_BASE,
    StatusCode,
    VMStatus,
  },
};
use move_vm_types::{
  // gas_schedule::NativeCostIndex,
  loaded_data::{
    types::FatType,
    runtime_types::Type,
  },
  // natives::function::native_gas,
};
use std::{
  cell::RefCell,
  collections::VecDeque,
  fmt::Debug,
  rc::Rc,
};
use vm::{
  errors::*,
};

use z3::{
  ast::{Ast, Array, Bool, BV, Dynamic, Datatype},
  Context,
  DatatypeSort,
  DatatypeBuilder,
  Sort,
};

use crate::types::{
  natives::{SymNativeResult, SymNativeContext},
  values::{
    values_impl::{SymValue, SymValueImpl, SymContainerRef, SymContainer, SymbolicContainerIndex},
    primitives::SymU64,
    struct_impl::{fat_type_to_sort},
    SymbolicMoveValue,
  },
};

#[derive(Debug)]
pub(super) struct SymVectorImpl<'ctx> {
  pub(super) context: &'ctx Context,
  pub(super) element_type: FatType,
  pub(super) datatype: Rc<RefCell<DatatypeSort<'ctx>>>,
  pub(super) data: Datatype<'ctx>,
}

impl<'ctx> SymVectorImpl<'ctx> {
  pub(super) fn copy_value(&self) -> Self {
    Self {
      context: self.context,
      element_type: self.element_type.clone(),
      datatype: Rc::clone(&self.datatype),
      data: self.data.translate(self.context),
    }
  }

  pub(super) fn equals(&self, other: &Self) -> Bool<'ctx> {
    self.data._eq(&other.data)
  }

  fn construct(&mut self, array: &Dynamic<'ctx>, len: &Dynamic<'ctx>) -> Datatype<'ctx>{
    self
      .datatype.borrow()
      .variants[0].constructor.apply(&[array, len])
      .as_datatype().unwrap()
  }

  pub(super) fn array(&self) -> Array<'ctx> {
    self.datatype.borrow().variants[0].accessors[0].apply(&[&Dynamic::from_ast(&self.data)]).as_array().unwrap()
  }

  fn set_array(&mut self, array: &Dynamic<'ctx>) {
    self.data = self.construct(array, &self.symbolic_len().into());
  }

  pub(super) fn symbolic_len(&self) -> BV<'ctx> {
    self.datatype.borrow().variants[0].accessors[1].apply(&[&Dynamic::from_ast(&self.data)]).as_bv().unwrap()
  }

  fn set_symbolic_len(&mut self, len: &Dynamic<'ctx>) {
    self.data = self.construct(&self.array().into(), len);
  }

  pub(super) fn get_raw(&self, idx: &Dynamic<'ctx>) -> Dynamic<'ctx> {
    // !!! how to check idx overflow?
    let v = self.array();
    v.select(idx)
  }

  pub(super) fn set_raw(&mut self, idx: &Dynamic<'ctx>, val: &Dynamic<'ctx>) {
    // !!! how to check idx overflow?
    let v = self.array();
    let v = v.store(idx, val);
    self.set_array(&v.into());
  }

  pub(super) fn set_multiple_raw(&mut self, idx_val_pairs: &[(&Dynamic<'ctx>, &Dynamic<'ctx>)]) {
    // !!! how to check idx overflow?
    let mut v = self.array();
    for (idx, val) in idx_val_pairs {
      v = v.store(idx, val);
    }
    self.set_array(&v.into());
  }

  pub(super) fn new(
    context: &'ctx Context,
    element_type: &FatType,
    values: &[&Dynamic<'ctx>],
  ) -> VMResult<Self> {
    let range_sort = fat_type_to_sort(context, element_type)?;
    let array_sort = Sort::array(context, &Sort::bitvector(context, 64), &range_sort);
    let vector_datatypesort = DatatypeBuilder::new(context)
      .variant("Vector", &[("array", &array_sort), ("length", &Sort::bitvector(context, 64))])
      .finish("Vector");

    let array = Array::fresh_const(context, "vector", &Sort::bitvector(context, 64), &range_sort);
    for i in 0..values.len() {
      array.store(&BV::from_u64(context, i as u64, 64).into(), &values[i]);
    }
    let symbolic_len = BV::from_u64(context, values.len() as u64, 64);
    let data = vector_datatypesort
      .variants[0].constructor.apply(&[&array.into(), &symbolic_len.into()])
      .as_datatype().unwrap();

    Ok(Self {
      context,
      element_type: element_type.clone(),
      datatype: Rc::new(RefCell::new(vector_datatypesort)),
      data,
    })
  }

  pub(super) fn empty(context: &'ctx Context, element_type: &FatType) -> VMResult<Self> {
    Self::new(context, element_type, &[])
  }

  pub(super) fn from_ast(context: &'ctx Context, element_type: &FatType, ast: Datatype<'ctx>) -> VMResult<Self> {
    let range_sort = fat_type_to_sort(context, element_type)?;
    let array_sort = Sort::array(context, &Sort::bitvector(context, 64), &range_sort);
    let vector_datatypesort = DatatypeBuilder::new(context)
      .variant("Vector", &[("array", &array_sort), ("length", &Sort::bitvector(context, 64))])
      .finish("Vector");

    Ok(Self {
      context,
      element_type: element_type.clone(),
      datatype: Rc::new(RefCell::new(vector_datatypesort)),
      data: ast,
    })
  }

  pub(super) fn push(&mut self, val: &Dynamic<'ctx>) {
    let len = self.symbolic_len();
    let v = self.array();
    let v = v.store(&Dynamic::from_ast(&len), val);
    let updated_len = len.bvadd(&BV::from_u64(self.context, 1, 64)).simplify();
    self.data = self.construct(&v.into(), &updated_len.into());
  }

  pub(super) fn pop(&mut self) -> Dynamic<'ctx> {
    let len = self.symbolic_len();
    let updated_len = len.bvsub(&BV::from_u64(self.context, 1, 64)).simplify();
    self.set_symbolic_len(&Dynamic::from_ast(&updated_len));
    let v = self.array();
    let res = v.select(&updated_len.into());
    res
  }

  pub(super) fn get(&self, idx: &SymbolicContainerIndex<'ctx>) -> VMResult<SymValue<'ctx>> {
    use SymbolicContainerIndex::*;

    let ast = match idx {
      Concrete(idx) => {
        let idx = BV::from_u64(self.context, *idx as u64, 64);
        self.get_raw(&Dynamic::from_ast(&idx))
      },
      Symbolic(idx) => self.get_raw(&idx.as_ast()?),
    };
    let ty = &self.element_type;
    Ok(SymValue::from_ast_with_type_info(self.context, ast, ty)?)
  }

  pub(super) fn set(
    &mut self,
    idx: &SymbolicContainerIndex<'ctx>,
    val: SymValue<'ctx>
  ) -> VMResult<()> {
    use SymbolicContainerIndex::*;

    match idx {
      Concrete(idx) => {
        let idx = BV::from_u64(self.context, *idx as u64, 64);
        self.set_raw(&Dynamic::from_ast(&idx), &val.as_ast()?);
      },
      Symbolic(idx) => self.set_raw(&idx.as_ast()?, &val.as_ast()?),
    };
    Ok(())
  }

  pub(super) fn swap(&mut self, idx1: &SymU64<'ctx>, idx2: &SymU64<'ctx>) -> VMResult<()> {
    let idx1 = idx1.as_ast()?;
    let idx2 = idx2.as_ast()?;
    let ast1 = self.get_raw(&idx1);
    let ast2 = self.get_raw(&idx2);
    self.set_multiple_raw(&[(&idx2, &ast1), (&idx1, &ast2)]);
    Ok(())
  }
}

impl<'ctx> SymbolicMoveValue<'ctx> for SymVectorImpl<'ctx> {
  fn as_ast(&self) -> VMResult<Dynamic<'ctx>> {
    Ok(Dynamic::from_ast(&self.data))
  }
}

/***************************************************************************************
*
* Vector
*
*   Native function imeplementations of the Vector module.
*
*   TODO: split the code into two parts:
*         1) Internal vector APIs that define & implements the core operations
           (and operations only).
*         2) Native function adapters that the dispatcher can call into. These will
*            check if arguments are valid and deal with gas metering.
*
**************************************************************************************/

pub const INDEX_OUT_OF_BOUNDS: u64 = NFE_VECTOR_ERROR_BASE + 1;
pub const POP_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 2;
pub const DESTROY_NON_EMPTY_VEC: u64 = NFE_VECTOR_ERROR_BASE + 3;

macro_rules! pop_arg_front {
  ($arguments:ident, $t:ty) => {
    $arguments.pop_front().unwrap().value_as::<$t>()?
  };
}

fn check_elem_layout<'ctx>(ty: &Type, v: &SymContainer<'ctx>) -> VMResult<()> {
  match (ty, &v) {
    (Type::U8, SymContainer::VecU8(_))
    | (Type::U64, SymContainer::VecU64(_))
    | (Type::U128, SymContainer::VecU128(_))
    | (Type::Bool, SymContainer::VecBool(_))
    | (Type::Address, SymContainer::Vector(_))
    | (Type::Signer, SymContainer::Vector(_))
    | (Type::Vector(_), SymContainer::Vector(_))
    | (Type::Struct(_), SymContainer::Vector(_)) => Ok(()),
    (Type::StructInstantiation(_, _), SymContainer::Vector(_)) => Ok(()),

    (Type::Reference(_), _) | (Type::MutableReference(_), _) | (Type::TyParam(_), _) => Err(
      VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
        .with_message(format!("invalid type param for vector: {:?}", ty)),
    ),

    (Type::U8, _)
    | (Type::U64, _)
    | (Type::U128, _)
    | (Type::Bool, _)
    | (Type::Address, _)
    | (Type::Signer, _)
    | (Type::Vector(_), _)
    | (Type::Struct(_), _)
    | (Type::StructInstantiation(_, _), _) => Err(
      VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR).with_message(format!(
        "vector elem layout mismatch, expected {:?}, got {:?}",
        ty, v
      )),
    ),
  }
}

pub fn native_empty<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.is_empty());

  let z3_ctx = context.get_z3_ctx();

  // let cost = native_gas(context.cost_table(), NativeCostIndex::EMPTY, 1);

  let ty_args = context.convert_to_fat_types(ty_args)?;

  let container = match &ty_args[0] {
    ty @ FatType::U8 => SymContainer::VecU8(SymVectorImpl::empty(z3_ctx, ty)?),
    ty @ FatType::U64 => SymContainer::VecU64(SymVectorImpl::empty(z3_ctx, ty)?),
    ty @ FatType::U128 => SymContainer::VecU128(SymVectorImpl::empty(z3_ctx, ty)?),
    ty @ FatType::Bool => SymContainer::VecBool(SymVectorImpl::empty(z3_ctx, ty)?),

    ty @ FatType::Address
    | ty @ FatType::Signer
    | ty @ FatType::Vector(_)
    | ty @ FatType::Struct(_) => SymContainer::Vector(SymVectorImpl::empty(z3_ctx, ty)?),

    FatType::Reference(_) | FatType::MutableReference(_) | FatType::TyParam(_) => {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message(format!("invalid type param for vector: {:?}", &ty_args[0])),
      )
    }
  };

  Ok(SymNativeResult::ok(
    // cost,
    vec![SymValue(SymValueImpl::new_container(container))],
  ))
}

pub fn native_length<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);

  let r = pop_arg_front!(args, SymContainerRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::LENGTH, 1);

  let v = r.borrow();
  check_elem_layout(&ty_args[0], &*v)?;
  let symbolic_len = match &*v {
    SymContainer::VecU8(v) => Ok(v.symbolic_len()),
    SymContainer::VecU64(v) => Ok(v.symbolic_len()),
    SymContainer::VecU128(v) => Ok(v.symbolic_len()),
    SymContainer::VecBool(v) => Ok(v.symbolic_len()),
    SymContainer::Vector(v) => Ok(v.symbolic_len()),
    _ => Err(
      VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
        .with_message("native_length on a non-vector container".to_string())
    ),
  }?;

  Ok(SymNativeResult::ok(/* cost, */vec![SymValue::from_sym_u64(SymU64::from_ast(symbolic_len))]))
}

pub fn native_push_back<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 2);

  let r = pop_arg_front!(args, SymContainerRef);
  let e = args.pop_front().unwrap();

  // let cost = native_gas(
  //   context.cost_table(),
  //   NativeCostIndex::PUSH_BACK,
  //   e.size().get() as usize,
  // );

  let mut v = r.borrow_mut();
  check_elem_layout(&ty_args[0], &*v)?;
  match &mut *v {
    SymContainer::VecU8(v)
    | SymContainer::VecU64(v)
    | SymContainer::VecU128(v)
    | SymContainer::VecBool(v)
    | SymContainer::Vector(v) => v.push(&e.as_ast()?),
    _ => {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("native_push_back on a non-vector container".to_string())
      );
    },
  };

  Ok(SymNativeResult::ok(/* cost, */vec![]))
}

pub fn native_borrow<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 2);

  let r = pop_arg_front!(args, SymContainerRef);
  let idx = pop_arg_front!(args, SymU64);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::BORROW, 1);

  let v = r.borrow();
  check_elem_layout(&ty_args[0], &*v)?;
  // TODO: check index out of bound?
  // if idx >= v.len() {
  //   return Ok(SymNativeResult::err(
  //     /* cost, */
  //     VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(INDEX_OUT_OF_BOUNDS),
  //   ));
  // }
  let v = SymValue(r.borrow_elem(SymbolicContainerIndex::Symbolic(idx))?);

  Ok(SymNativeResult::ok(/* cost, */vec![v]))
}

pub fn native_pop<'ctx>(
  context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);

  let r = pop_arg_front!(args, SymContainerRef);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::POP_BACK, 1);

  let mut v = r.borrow_mut();
  check_elem_layout(&ty_args[0], &*v)?;

  // TODO: how to check if empty?
  // macro_rules! err_pop_empty_vec {
  //   () => {
  //     return Ok(SymNativeResult::err(
  //       // cost,
  //       VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(POP_EMPTY_VEC),
  //     ));
  //   };
  // }

  // let res = match &mut *v {
  //   SymContainer::VecU8(v) => match v.pop() {
  //     Some(x) => SymValue::from_sym_u8(x),
  //     None => err_pop_empty_vec!(),
  //   },
  //   SymContainer::VecU64(v) => match v.pop() {
  //     Some(x) => SymValue::from_sym_u64(x),
  //     None => err_pop_empty_vec!(),
  //   },
  //   SymContainer::VecU128(v) => match v.pop() {
  //     Some(x) => SymValue::from_sym_u128(x),
  //     None => err_pop_empty_vec!(),
  //   },
  //   SymContainer::VecBool(v) => match v.pop() {
  //     Some(x) => SymValue::from_sym_bool(x),
  //     None => err_pop_empty_vec!(),
  //   },

  //   SymContainer::Vector(v) => match v.pop() {
  //     Some(x) => SymValue(x),
  //     None => err_pop_empty_vec!(),
  //   },
  //   _ => {
  //     return Err(
  //       VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
  //         .with_message("native_length on a non-vector container".to_string())
  //     );
  //   },
  // };

  let res = match &mut *v {
    SymContainer::VecU8(v)
    | SymContainer::VecU64(v)
    | SymContainer::VecU128(v)
    | SymContainer::VecBool(v)
    | SymContainer::Vector(v) => SymValue::from_ast_with_type_info(
      context.get_z3_ctx(),
      v.pop(),
      &v.element_type
    )?,
    _ => {
      return Err(
        VMStatus::new(StatusCode::UNKNOWN_INVARIANT_VIOLATION_ERROR)
          .with_message("native_length on a non-vector container".to_string())
      );
    },
  };

  Ok(SymNativeResult::ok(/* cost, */vec![res]))
}

// TODO: how can we check if a vector is empty? or just destory it
pub fn native_destroy_empty<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 1);
  let v = args.pop_front().unwrap().value_as::<SymContainer>()?;

  // let cost = native_gas(context.cost_table(), NativeCostIndex::DESTROY_EMPTY, 1);

  check_elem_layout(&ty_args[0], &v)?;

  // let is_empty = match &v {
  //   SymContainer::U8(v) => v.is_empty(),
  //   SymContainer::U64(v) => v.is_empty(),
  //   SymContainer::U128(v) => v.is_empty(),
  //   SymContainer::Bool(v) => v.is_empty(),

  //   SymContainer::General(v) => v.is_empty(),
  // };

  // if is_empty {
  //   Ok(SymNativeResult::ok(cost, vec![]))
  // } else {
  //   Ok(SymNativeResult::err(
  //     // cost,
  //     VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(DESTROY_NON_EMPTY_VEC),
  //   ))
  // }
  Ok(SymNativeResult::ok(vec![]))
}

pub fn native_swap<'ctx>(
  _context: &impl SymNativeContext<'ctx>,
  ty_args: Vec<Type>,
  mut args: VecDeque<SymValue<'ctx>>,
) -> VMResult<SymNativeResult<'ctx>> {
  debug_assert!(ty_args.len() == 1);
  debug_assert!(args.len() == 3);
  let r = pop_arg_front!(args, SymContainerRef);
  let idx1 = pop_arg_front!(args, SymU64);
  let idx2 = pop_arg_front!(args, SymU64);

  // let cost = native_gas(context.cost_table(), NativeCostIndex::SWAP, 1);

  let mut v = r.borrow_mut();
  check_elem_layout(&ty_args[0], &*v)?;

  // TODO: how can we check idx out of bound?
  // macro_rules! swap {
  //   ($v: ident) => {{
  //     if idx1 >= $v.len() || idx2 >= $v.len() {
  //       return Ok(SymNativeResult::err(
  //         /* cost, */
  //         VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR).with_sub_status(INDEX_OUT_OF_BOUNDS),
  //       ));
  //     }
  //     $v.swap(idx1, idx2);
  //   }};
  // }

  match &mut *v {
    SymContainer::VecU8(v)
    | SymContainer::VecU64(v)
    | SymContainer::VecU128(v)
    | SymContainer::VecBool(v)
    | SymContainer::Vector(v) => v.swap(&idx1, &idx2)?,
    _ => {
      return Ok(SymNativeResult::err(
        VMStatus::new(StatusCode::NATIVE_FUNCTION_ERROR)
          .with_message(format!("Cannot call native_swap on non-vector container {:?}", v))
      ));
    }
  }

  Ok(SymNativeResult::ok(/* cost, */vec![]))
}