use crate::{
    plugin::Plugin,
    runtime::interpreter::SymInterpreter,
    types::values::SymIntegerValue,
};

use libra_types::{
  vm_error::{StatusCode, VMStatus},
};

use vm::{
  errors::*,
  file_format::Bytecode,
};

use bytecode_verifier::{control_flow_graph::{ControlFlowGraph,BlockId}};
use z3::{ast::{Bool},Context,Solver,SatResult};

pub struct GeneratedDataFlow{
  flow:Vec<Vec<i32>>,
}

pub fn flow_is_diff(flow1:GeneratedDataFlow, flow2:GeneratedDataFlow, z3_ctx: Context)->bool{
  let solver = Solver::new(&z3_ctx);
  if flow1.flow.len()==flow2.flow.len() {
    println!("-------TOD Detected at flow: line unmatched -------" );
    return true;
  }
  let n = flow1.flow.len();

  for i in 0..n {
    if flow1.flow[i] == flow2.flow[i] {
      continue;
    }
  let tx_cd = Bool::or(&z3_ctx,
            &[&Bool::not(&Bool::from_bool(&z3_ctx,flow1.flow[i][0]==flow2.flow[i][0])),
            &Bool::not(&Bool::from_bool(&z3_ctx,flow1.flow[i][1]==flow2.flow[i][1])),
            &Bool::not(&Bool::from_bool(&z3_ctx,flow1.flow[i][2]==flow2.flow[i][2])),],
        );  
  solver.assert(&tx_cd.not());
  match solver.check(){
    SatResult::Sat =>{
      println!("-------TOD Detected at flow{:?}: flow diff -------",flow1.flow[i] );
      return true;
    }
    _ => {}
  }

  }

    return false;
}


pub struct CFGRelatedPlugin<'ctx> {
  context: &'ctx Context,
  // specs: HashMap< <'a, 'ctx>>,
}

//tod 
impl<'a, 'ctx> CFGRelatedPlugin<'ctx> {
  pub fn new(context: &'ctx Context) -> Self {
    Self {
      context,
      // specs: HashMap::new(),
      
    }
  }
}
impl<'a, 'ctx> Plugin<'ctx> for CFGRelatedPlugin<'a> {
  fn on_before_execute_instrcution<'vtxn>(
    &self,
    interpreter: &mut SymInterpreter<'vtxn, 'ctx>,
    instruction: &Bytecode
  ) -> VMResult<()>{
    Ok(())
  }
}