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

  /// State of VM Evaluation:
  /// A Store, an Environment, a Stack (of Evaluation Frames), and an expression.
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct State {
    pub store: List<(Loc, Val)>,
    pub env:   List<(Var, Val)>,
    /// TODO: Do we need an environment for App frames? It seems like we do not.
    pub stack: List<Eval>,
    /// Using a PExp here, not an Exp, because of https://github.com/rust-lang/rust/issues/16223
    pub pexp:  PExp, 
  }
  /// Evaluation Contexts (one "Frame" only); The full context is
  /// given by a stack of frames.
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum Eval {
    /// Apply the function of the current computation to a (closed)
    /// value term, given by this frame.
    App(Val),
    /// Using the frame's variable and environment, bind the (closed)
    /// value produced by the current computation and run the
    /// expression given by this frame.
    Let(Var, Env, Exp), 
  }
  /// Pre-Expressions
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum PExp {
    Force(Val),
    Ret(Val),
    Lam(Var,Exp),
    // App: First sub-term is an expression, since we don't want to
    // let-bind partial applications of multiple-argument functions.
    // See oapp! macro, defined below.  This syntactic form is in the
    // style of CBPV.
    App(Exp,Val), 
    Proj(Val,Val),
    Ann(Box<PExp>,PVal),
    Ref(Val),
    Get(Val),
    Set(Val,Val),
    Ext(Val,Val,Val),
    Let(Var,Exp,Exp),    
  }
  /// Expressions: A Pre-Expression, along with an annotation
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct Exp {    
    pub pexp:Box<PExp>,
    pub ann:super::refl::Ann,
  }
  /// Pre-Values
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum PVal {
    Thunk(Env,Exp),
    Dict(Dict),
    Num(isize),
    Str(String),
    Loc(Loc),
    Var(Var),    
  }
  /// Values: A Pre-Value, along with an annotation
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct Val {
    pub pval:Box<PVal>,
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
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! othunk {
  [ $body:expr ] => {{
    let pval = obj::PVal::Thunk( <List<(obj::Var, obj::Val)> as ListIntro<_>>::nil(), $body );
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
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
    obj::Val{pval:Box::new(obj::PVal::Var(stringify!($var).to_string())),
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
macro_rules! ovarf {
  ( $var:ident ) => {{ obj::Exp{pexp:Box::new(obj::PExp::Force(
    obj::Val{pval:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             ann:refl::Typ::Top})),
                                ann:refl::Typ::Top }
  }};
}

pub fn is_final(exp:&obj::PExp) -> bool {
  match *exp {
    obj::PExp::Ret(_)   => true,
    obj::PExp::Lam(_,_) => true,
    _ => false,
  }
}

pub fn close_pval(env:&obj::Env, v:obj::PVal) -> obj::PVal {
  panic!("")
}

pub fn close_val(env:&obj::Env, v:obj::Val) -> obj::Val {
  obj::Val{pval:Box::new(close_pval(env, *v.pval)), ..v}
}

pub fn initial_state(e:obj::PExp) -> obj::State {
  obj::State{store:<List<_> as ListIntro<_>>::nil(),
             stack:<List<_> as ListIntro<_>>::nil(),
             env:  <List<_> as ListIntro<_>>::nil(),
             pexp: e}
}

pub fn small_step(st:obj::State) -> Option<obj::State> {
  use obj::*;
  use adapton::collections::*;

  if is_final(&st.pexp) {
    if list_is_empty(&st.stack) { None }
    else {
      let (fr, stack) = list_pop(st.stack);
      match (fr, st.pexp) {
        (Eval::App(v), PExp::Lam(x,e)) =>        Some(State{env:list_push(st.env,(x,v)), stack:stack, pexp:*e.pexp, ..st}),
        (Eval::Let(x,fr_env,e), PExp::Ret(v)) => Some(State{env:list_push(fr_env,(x,v)), stack:stack, pexp:*e.pexp, ..st}),
        _ => panic!("invalid state: current stack and (final) expression do not match.")
      }}
  }
  else {
    let st = match st.pexp {
      PExp::Ann(e,_) => { State{pexp:*e, ..st} }
      PExp::App(e, v) => {
        let stack = list_push(st.stack, Eval::App(close_val(&st.env, v)));
        State{stack:stack, pexp:*e.pexp, ..st}
      }
      PExp::Let(x,e1,e2) => {
        let stack = list_push(st.stack, Eval::Let(x,st.env.clone(),e2));
        State{stack:stack, pexp:*e1.pexp, ..st}
      }
      PExp::Force(v) => {
        match *close_val(&st.env,v).pval {
          PVal::Thunk(env,e) => State{env:env, pexp:*e.pexp, ..st},
          _ => panic!("stuck: forced a value that is not a thunk")
        }
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
    olet!{ authors   = oapp!(ovarf!(openDb), ostr!("authors.csv")),
           authorsUS = oapp!(ovarf!(filterDb), ovar!(authors),
                             othunk![ olam!(author.
                                            olet!{c = oproj!(ovar!(author), ostr!("citizenship")) ;
                                                  oapp!(ovarf!(eq), ovar!(c), ostr!("US"))}
                                            )]
                             ),
           books     = oapp!(ovarf!(openDb), ostr!("books.csv")),
           authbksUS = oapp!(ovarf!(joinDb),
                             ovar!(authorsUS),
                             othunk![ olam!(author. oproj!(ovar!(author), ostr!("name"))) ],
                             ovar!(books),
                             othunk![ olam!(book. oproj!(ovar!(book), ostr!("author"))) ]
                             )
           ;
           ovarf!(halt)
    };

  let mut st = initial_state(*example.pexp);
  loop {
    println!("{:?}\n", st);
    match small_step(st) {
      None      => break,
      Some(st2) => st = st2
    }
  }
}
