//#[macro_use]
extern crate adapton;
use adapton::collections::{List};
//use adapton::engine::*;
//use adapton::macros::*;
//use std::rc::Rc;  

mod refl {
  use std::collections::HashMap;
  use adapton::collections::{List};
  
  #[derive(Debug,PartialEq,Eq,Hash)]
  pub enum Typ {
    Top,
    Arr(Box<Typ>, Box<Typ>),
    Num,
    Str,
    Dict(Box<Dict>),
    Ref(Box<Typ>)
  }
  //pub type Dict = HashMap<super::obj::Val,Typ>;
  pub type Dict = List<(super::obj::Val, Typ)>;
  pub type Ann = Typ;
}

mod obj {
  use std::collections::HashMap;  
  use adapton::collections::{List};
  
  pub type Loc = usize;
  pub type Var = String;

  #[derive(Debug,PartialEq,Eq,Hash)]
  pub enum PExp {
    Lam(Var,Exp),
    App(Val,Val),
    Proj(Val,Val),
    Val(Val),
    Ann(Box<PExp>,PVal),
    Ref(Val),
    Get(Val),
    Set(Val,Val),
    Ext(Val,Val,Val),
    Let(Var,Exp,Exp),    
  }
  #[derive(Debug,PartialEq,Eq,Hash)]
  pub struct Exp {    
    pub exp:Box<PExp>,
    pub ann:super::refl::Ann,
  }
  #[derive(Debug,PartialEq,Eq,Hash)]
  pub enum PVal {
    Clos(Env,Exp),
    Dict(Dict),
    Num(isize),
    Str(String),
    Loc(Loc),
    Var(Var),    
  }
  #[derive(Debug,PartialEq,Eq,Hash)]
  pub struct Val {
    pub val:Box<PVal>,
    pub ann:super::refl::Ann,
  }
  pub type Dict = List<(Val,Val)>;
  pub type Env  = List<(Var,Val)>;
  //pub type Dict = HashMap<Val,Val>;
  //pub type Env  = HashMap<Var,Val>;
}

macro_rules! olet {
  { $var:ident = $rhs:expr ; $body:expr } => {{
    obj::Exp{exp:Box::new(obj::PExp::Let(stringify!($var).to_string(), $rhs, $body)),
             ann:refl::Typ::Top}
  }};
}

macro_rules! ovar {
  ( $var:ident ) => {{ obj::Exp{exp:Box::new(obj::PExp::Val(
    obj::Val{val:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             ann:refl::Typ::Top})),
                                ann:refl::Typ::Top }
  }};
}

// macro_rules! olet (
//   ( $var:ident := $rhs:expr ; $body:expr ) => { 1
//     // obj::Exp{exp:obj::Pexp::Let
//     //          ("foo",
//     //           obj::Exp{exp:Box::new($rhs); ann:refl::Typ::Top},
//     //           obj::Exp{exp:Box::new($body); ann:refl::Typ::Top}
//     //           ),
//     //          ann:refl::Typ::Top
//     // }
//   };
//   )

fn main() {
  use obj::*;

  let example =
    olet!{ authors = ovar!(undef) ;
           ovar!(undef) };
  
  println!("{:?}", example);
  drop(example)
  
  // let example = ( olet! "authors"    := oapp!(ovar!("openDb", ostr!("authors.csv"))) ;
  //                 olet! "authorsUS"  := oapp!(oapp!(
  //                   ovar!("filterDb", ovar!("authors"),
  //                         olam!("x", oapp!(oapp!(ovar!("=="),
  //                                                oproj!(ovar!("x"),
  //                                                       ostr!("citizenship"),
  //                                                       )), ostr!("US"))))
  //                     )) ;
  //                 ovar!("authorsUS") );
}
