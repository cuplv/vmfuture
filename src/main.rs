extern crate csv;

//#[macro_use]
extern crate adapton;
use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
//use std::rc::Rc;  

pub mod refl {
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

pub mod obj {  
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
    pub nloc:  usize,
    pub env:   List<(Var, Val)>,
    /// TODO: Do we need an environment for App frames? It seems like we do not.
    pub stack: List<Frame>,
    /// Using a PExp here, not an Exp, because of https://github.com/rust-lang/rust/issues/16223
    pub pexp:  PExp, 
  }
  /// Evaluation Contexts (one "Frame" only); The full context is
  /// given by a stack of frames.
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum Frame {
    /// As a function, apply the current computation to the (closed)
    /// value argument given by this frame.
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
    OpenThunk(Exp),
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
macro_rules! ovar {
  ( $var:ident ) => {{
    obj::Val{pval:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             ann:refl::Typ::Top}
  }};
}

#[macro_export]
macro_rules! ostr {
  ( $str:expr ) => {{
    let pval = obj::PVal::Str( $str.to_string() );
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! oloc {
  ( $loc:expr ) => {{
    let pval = obj::PVal::Loc( $loc );
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! ounit {
  ( ) => {{
    let pval = obj::PVal::Dict( List::Nil );
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! odict {
  ( $dict:expr ) => {{
    let pval = obj::PVal::Dict( $dict );
    obj::Val{pval:Box::new(pval), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! othunk {
  [ $body:expr ] => {{
    let pval = obj::PVal::OpenThunk( $body );
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
macro_rules! oproj {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Proj( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! ovarf {
  ( $var:ident ) => {{
    let v = ovar!($var);
    obj::Exp{pexp:Box::new(obj::PExp::Force(v)),
             ann:refl::Typ::Top}
  }};
}

#[macro_export]
macro_rules! oref {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ref( $val );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! oget {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Get( $val );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! oset {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Set( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

#[macro_export]
macro_rules! oret {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ret( $val );
    obj::Exp{pexp:Box::new(pexp), ann:refl::Typ::Top}
  }}
}

pub fn is_final(exp:&obj::PExp) -> bool {
  match *exp {
    obj::PExp::Ret(_)   => true,
    obj::PExp::Lam(_,_) => true,
    _ => false,
  }
}

pub fn close_pval(env:&obj::Env, v:obj::PVal) -> obj::PVal {
  use obj::PVal::*;
  match v {
    OpenThunk(e)  => Thunk(env.clone(), e),
    Thunk(env2,e) => Thunk(env2,e),
    Dict(List::Nil) => Dict(List::Nil),
    Dict(dict)    => panic!("TODO: fold over dictionary"),
    Num(n)        => Num(n),
    Str(s)        => Str(s),
    Loc(l)        => Loc(l),
    Var(x)        => match <List<_> as MapElim<_,_>>::find(env, &x) {
      Some(v)     => *v.pval,
      None        => panic!("stuck: close_pval: Unbound variable: `{}'", x)
    }
  }
}

pub fn close_val(env:&obj::Env, v:obj::Val) -> obj::Val {
  obj::Val{pval:Box::new(close_pval(env, *v.pval)), ..v}
}

pub fn initial_state(e:obj::PExp) -> obj::State {
  obj::State{store:<List<_> as ListIntro<_>>::nil(),
             nloc: 0,
             stack:<List<_> as ListIntro<_>>::nil(),
             env:  <List<_> as ListIntro<_>>::nil(),
             pexp: e}
}

pub fn small_step(st:obj::State) -> Result<obj::State, obj::State> {
  use obj::*;
  use obj::PExp::*;
  use adapton::collections::*;

  if is_final(&st.pexp) {
    if list_is_empty(&st.stack) { Err(st) }
    else {
      let (fr, stack) = list_pop(st.stack);
      match (fr, st.pexp) {
        (Frame::App(v), Lam(x,e)) => 
          Ok(State{env:list_push(st.env,(x,v)), stack:stack, pexp:*e.pexp, ..st}),
        (Frame::Let(x,fr_env,e), Ret(v)) => {
          let v = close_val(&st.env, v);
          Ok(State{env:list_push(fr_env,(x,v)), stack:stack, pexp:*e.pexp, ..st})
        },
        _ => panic!("invalid state: current stack and (final) expression do not match.")
      }}
  }
  else {
    let st = match st.pexp {
      Ann(e,_) => { State{pexp:*e, ..st} }
      App(e, v) => {
        let stack = list_push(st.stack, Frame::App(close_val(&st.env, v)));
        State{stack:stack, pexp:*e.pexp, ..st}
      }
      Let(x,e1,e2) => {
        let stack = list_push(st.stack, Frame::Let(x,st.env.clone(),e2));
        State{stack:stack, pexp:*e1.pexp, ..st}
      }
      Force(v) => {
        match *close_val(&st.env,v).pval {
          PVal::Thunk(env,e) => State{env:env, pexp:*e.pexp, ..st},
          _ => panic!("stuck: forced a value that is not a thunk")
        }
      }      
      Ref(v) => {
        let v = close_val(&st.env,v) ;
        let store = <List<_> as MapIntro<_,_>>::update(st.store, st.nloc, v);
        State{nloc:st.nloc+1, store:store, pexp:Ret(oloc!(st.nloc)), ..st}
      }
      Set(v1,v2) => {
        let v1 = close_val(&st.env, v1);
        let v2 = close_val(&st.env, v2);
        match *v1.pval {
          PVal::Loc(loc) => {
            let store = <List<_> as MapIntro<_,_>>::update(st.store, loc, v2);
            State{store:store, pexp:Ret(ounit!()), ..st}
          }
          _ => panic!("stuck: ref-set on a non-location: {:?}", v1)
        }        
      }
      Get(v) => {
        let v = close_val(&st.env,v) ;
        match *v.pval {
          PVal::Loc(loc) => {          
            let w = <List<_> as MapElim<_,_>>::find(&st.store, &loc);
            match w {
              None => panic!("internal error: ref-get dereferenced non-existent store location"),
              Some(w) => State{pexp:Ret(w),.. st}
            }
          }
          _ => panic!("stuck: ref-get on a non-location: {:?}", v)
        }
      }      
      Proj(v1,v2) => {
        let v1 = close_val(&st.env,v1) ;
        let v2 = close_val(&st.env,v2) ;
        match *v1.pval {
          PVal::Dict(dict) => {          
            let w = <List<_> as MapElim<_,_>>::find(&dict, &v2);
            match w {
              None => panic!("stuck: dict-proj failed on projection of given value: {:?}", v2),
              Some(w) => State{pexp:Ret(w),.. st}
            }
          }
          _ => panic!("stuck: dict-proj on a non-dictionary: {:?}", v1)
        }
      }
      Ext(v1,v2,v3) => {
        let v1 = close_val(&st.env, v1);
        let v2 = close_val(&st.env, v2);
        let v3 = close_val(&st.env, v3);
        match *v1.pval {
          PVal::Dict(dict) => {
            let dict = <List<_> as MapIntro<_,_>>::update(dict, v2, v3);
            State{pexp:Ret(odict!(dict)), ..st}
          }
          _ => panic!("stuck: dict-ext on a non-dictionary: {:?}", v1)
        }
      }      
      // These are terminal cases, and thus are excluded in this match:
      Ret(_)   => unreachable!(),
      Lam(_,_) => unreachable!(),
    };
    Ok(st)
  }
}

fn eval (st:obj::State) -> obj::State {
  let mut st = st;
  loop {
    println!("{:?}\n", st);
    match small_step(st) {
      Ok(st2)  => st = st2,
      Err(st2) => { 
        println!("halted:\n{:?}", st2); 
        return st2
      },
    }
  }
}

#[test]
fn test_store() {  
  let example : obj::Exp =
    olet!{ x  = oref!(ostr!("apple")),
           y1 = oget!(ovar!(x)),
           z  = oset!(ovar!(x), ostr!("banana")),
           y2 = oget!(ovar!(x))
           ;
           oret!(ovar!(y2))
    };
  let st = initial_state(*example.pexp);
  let st = eval(st);
  let y2 = <List<_> as MapElim<_,_>>::find(&st.env, &"y2".to_string());
  assert!( y2 == Some(ostr!("banana")) )  
}

#[test]
fn test_listing_1() {
  listing_1()
}

fn listing_1() {
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
  let st = initial_state(*example.pexp);
  drop(eval(st));
}

fn main() {
  //use obj::*;
  listing_1()
}
