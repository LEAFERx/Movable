use libra_types::{
  identifier::IdentStr,
};
use std::{
  path::{Path, PathBuf},
};
use structopt::StructOpt;

use z3::{Config, Context};

#[derive(Debug, StructOpt)]
struct Args {
  #[structopt(parse(from_os_str))]
  pub source: PathBuf,
  #[structopt(name = "function name", short, long)]
  pub func: String,
}

fn main() {
  let args = Args::from_args();
  let _path = Path::new(&args.source);
  let _function_name = IdentStr::new(args.func.as_str()).unwrap();

  let config = Config::new();
  let _context = Context::new(&config);

  unimplemented!()
}
