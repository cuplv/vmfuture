//#[macro_use]
//extern crate adapton;
//use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
//use std::rc::Rc;  

mod refl {
  use std::collections::HashMap;

  pub enum Typ {
    Top,
    Arr(Box<Typ>, Box<Typ>),
    Num,
    Str,
    Dict(Box<Dict>),
    Ref(Box<Typ>)
  }
  pub type Dict = HashMap<super::obj::Val,Typ>;
  pub type Ann = Typ;
}

mod obj {
  use std::collections::HashMap;  

  pub type Loc = usize;
  pub type Var = String;
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
  pub struct Exp {
    exp:Box<PExp>,
    ann:super::refl::Ann,
  }
  pub enum PVal {
    Clos(Env,Exp),
    Dict(Dict),
    Num(isize),
    Str(String),
    Loc(Loc),
    Var(Var),    
  }
  pub struct Val {
    val:Box<PVal>,
    ann:super::refl::Ann,
  }
  pub type Dict = HashMap<Val,Val>;
  pub type Env  = HashMap<Var,Val>;
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
