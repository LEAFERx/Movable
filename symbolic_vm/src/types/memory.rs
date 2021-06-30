use z3::{
  ast::{Datatype},
  datatype_builder::create_datatypes,
  Context,
  DatatypeAccessor,
  DatatypeBuilder,
  DatatypeSort,
  Sort,
};

// use crate::{
//   types::{
//     values::{
//       types::{SymStructTag, SymTypeTag, make_tag_datatype_sorts},
//     }
//   }
// };

struct SymMemory<'ctx> {
  ast: Datatype<'ctx>,
}
