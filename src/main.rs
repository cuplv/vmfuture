//#[macro_use]
extern crate adapton;
use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
//use std::rc::Rc;  

mod refl {
  //use std::collections::HashMap;
  use adapton::collections::{List};
  
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
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
  //use super::*;
  //use std::collections::HashMap;
  use adapton::collections::*;
  
  pub type Loc = usize;
  pub type Var = String;

  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct State {
    pub store: List<(Loc, Val)>,
    pub env:   List<(Var, Val)>,
    /// TODO: Do we need an environment for App frames? It seems like we do not.
    pub stack: List<(Env, Eval)>, 
    /// Using a PExp here, not an Exp, because of https://github.com/rust-lang/rust/issues/16223
    pub pexp:  PExp, 
  }
    
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum Eval {
    App(Val),
    Let(Var, Exp),
  }
  
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum PExp {
    Ret(Val),
    Lam(Var,Exp),
    // App: First sub-term is an expression, since we don't want to
    // let-bind partial applications of multiple-argument functions.
    // See oapp! macro, defined below.
    App(Exp,Val), 
    Proj(Val,Val),
    Ann(Box<PExp>,PVal),
    Ref(Val),
    Get(Val),
    Set(Val,Val),
    Ext(Val,Val,Val),
    Let(Var,Exp,Exp),    
  }
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct Exp {    
    pub pexp:Box<PExp>,
    pub ann:super::refl::Ann,
  }
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum PVal {
    Thunk(Env,Exp),
    Dict(Dict),
    Num(isize),
    Str(String),
    Loc(Loc),
    Var(Var),    
  }
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct Val {
    pub val:Box<PVal>,
    pub ann:super::refl::Ann,
  }
  pub type Dict = List<(Val,Val)>;
  pub type Env  = List<(Var,Val)>;
  //pub type Dict = HashMap<Val,Val>;
  //pub type Env  = HashMap<Var,Val>;
}

#[macro_export]
macro_rules! oproj {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Proj( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! ostr {
  ( $str:expr ) => {{
    let pval = obj::PVal::Str( $str.to_string() );
    obj::Val{val:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! othunk {
  [ $body:expr ] => {{
    let pval = obj::PVal::Thunk( <List<(obj::Var, obj::Val)> as ListIntro<_>>::nil(), $body );
    obj::Val{val:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! olam {
  { $var:ident . $body:expr } => {{
    let pexp = obj::PExp::Lam(stringify!($var).to_string(), $body);
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }};
  { $var1:ident . ( $var2:ident).+ . $body:expr } => {{
    olam!($var . olam!( ( $var2 ).+ . $body ) )
  }}
}

#[macro_export]
macro_rules! olet {
  { $var:ident = $rhs:expr ; $body:expr } => {{
    let pexp = obj::PExp::Let(stringify!($var).to_string(), $rhs, $body);
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }};
  { $var1:ident = $rhs1:expr , $( $var2:ident = $rhs2:expr ),+ ; $body:expr } => {{
    olet!($var1 = $rhs1 ; olet!( $( $var2 = $rhs2 ),+ ; $body ))
  }};
}

#[macro_export]
macro_rules! ovar {
  ( $var:ident ) => {{
    obj::Val{val:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             ann:refl::Typ::Top}
  }};
}

#[macro_export]
macro_rules! oapp {
  ( $exp:expr ) => {{ $exp }}
  ;
  ( $exp:expr , $val:expr ) => {{
    let pexp = obj::PExp::App($exp, $val);
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
  ;
  ( $exp:expr , $val1:expr , $( $val2:expr ),+ ) => {{
    oapp!( oapp!($exp, $val1), $( $val2 ),+ )
  }}  
}

#[macro_export]
macro_rules! ovare {
  ( $var:ident ) => {{ obj::Exp{pexp:Box::new(obj::PExp::Ret(
    obj::Val{val:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             ann:refl::Typ::Top})),
                                ann:refl::Typ::Top }
  }};
}

pub fn is_final(exp:&obj::PExp) -> bool {
  match *exp {
    obj::PExp::Ret(_)   => true,
    obj::PExp::Lam(_,_) => true,
    obj::PExp::Ann(ref e, _) => is_final(e),
    _ => false,
  }
}

pub fn small_step(st:obj::State) -> Option<obj::State> {
  use obj::*;
  use adapton::collections::*;

  if is_final(&st.pexp) {
    if list_is_empty(&st.stack) { None }
    else {
      let ((env,eval), stack) = list_pop(st.stack);
      match (eval, st.pexp) {
        (Eval::App(v), PExp::Lam(x,e)) =>
          Some(State{env:list_push(env, (x,v)),
                     stack:stack, pexp:*e.pexp, ..st}),
        (Eval::Let(x,e), PExp::Ret(v)) =>
          Some(State{env:list_push(env, (x,v)),
                     stack:stack, pexp:*e.pexp, ..st}),
        _ => panic!("invalid state: current stack and (final) expression do not match.")
      }}
  }
  else {
    let st = match st.pexp {
      PExp::App(e, v) => {
        let frame = (st.env.clone(), Eval::App(v));
        let stack = list_push(st.stack, frame);
        State{stack:stack, pexp:*e.pexp, ..st}
      }
      PExp::Ann(e,_) => {
        State{pexp:*e, ..st}
      }
      PExp::Let(x,e1,e2) => {
        let frame = (st.env.clone(), Eval::Let(x,e2));
        let stack = list_push(st.stack, frame);
        State{stack:stack, pexp:*e1.pexp, ..st}
      }
      PExp::Ref(v) => unimplemented!(),
      PExp::Get(v) => unimplemented!(),
      
      PExp::Proj(v1,v2) => unimplemented!(),
      PExp::Set(v1,v2) => unimplemented!(),
      PExp::Ext(v1,v2,v3) => unimplemented!(),
      
      // These are terminal cases, and thus are excluded in this match:
      obj::PExp::Ret(_)   => unreachable!(),
      obj::PExp::Lam(_,_) => unreachable!(),
    };
    Some(st)
  }
}

fn main() {
  //use obj::*;

  let example : obj::Exp =
    olet!{ authors   = oapp!(ovare!(openDb), ostr!("authors.csv")),
           authorsUS = oapp!(ovare!(filterDb), ovar!(authors),
                             othunk![ olam!(author.
                                            olet!{c = oproj!(ovar!(author), ostr!("citizenship")) ;
                                                  oapp!(ovare!(eq), ovar!(c), ostr!("US"))}
                                            )]
                             ),
           books     = oapp!(ovare!(openDb), ostr!("books.csv")),
           authbksUS = oapp!(ovare!(joinDb),
                             ovar!(authorsUS),
                             othunk![ olam!(author. oproj!(ovar!(author), ostr!("name"))) ],
                             ovar!(books),
                             othunk![ olam!(book. oproj!(ovar!(book), ostr!("author"))) ]
                             )
           ;
           ovare!(undef)
    };
  
  println!("{:?}", example);
  drop(example) 
}
