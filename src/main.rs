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
  pub enum CTyp {
    Top, 
    F(Box<VTyp>), // Ret
    Arr(Box<VTyp>, Box<CTyp>), // ->
  }
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum VTyp {
    Top,
    Num,
    Str,
    Dict(Box<Dict>),
    Ref(Box<VTyp>),
    U(Box<CTyp>), // Thunk
  }
  //pub type Dict = HashMap<super::obj::Val,Typ>;
  pub type Dict = List<(super::obj::Val, VTyp)>;
  pub type VAnn = VTyp;
  pub type CAnn = CTyp;
  pub type TEnv = List<(super::obj::Var, VTyp)>;

  pub fn do_pass(st:super::obj::State) -> Option<super::obj::State> { super::chk_state(st) }
}

pub mod obj {  
  //use super::*;
  //use std::collections::HashMap;
  use adapton::collections::*;

  pub type Loc = usize;
  pub type Var = String;

  pub type Stack = List<Frame>;
  pub type Env   = List<(Var, Val)>;
  pub type Store = List<(Loc, Val)>;

  /// State of VM Evaluation:
  /// A Store, an Environment, a Stack (of Evaluation Frames), and an expression.
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct State {
    pub store: Store,
    pub nloc:  usize,
    pub env:   Env,
    /// TODO: Do we need an environment for App frames? It seems like we do not.
    pub stack: Stack,
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

  /// Primitives
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum Prim {
    Halt,
    DbOpen,
    DbFilter,
    DbJoin,
    Eq,
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
    Ann(Box<PExp>,super::refl::CTyp),
    Ref(Val),
    Get(Val),
    Set(Val,Val),
    Ext(Val,Val,Val),
    Let(Var,Exp,Exp),    
    Prim(Prim),
  }
  /// Expressions: A Pre-Expression, along with an annotation
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub struct Exp {    
    pub pexp:Box<PExp>,
    pub cann:super::refl::CAnn,
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
    pub vann:super::refl::VAnn,
  }
  pub type Dict = List<(Val,Val)>;
  //pub type Env  = List<(Var,Val)>;
  //pub type Dict = HashMap<Val,Val>;
  //pub type Env  = HashMap<Var,Val>;
}


#[macro_export]
macro_rules! ovar {
  ( $var:ident ) => {{
    obj::Val{pval:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             vann:refl::VTyp::Top}
  }};
}

#[macro_export]
macro_rules! ostr {
  ( $str:expr ) => {{
    let pval = obj::PVal::Str( $str.to_string() );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! oloc {
  ( $loc:expr ) => {{
    let pval = obj::PVal::Loc( $loc );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! ounit {
  ( ) => {{
    let pval = obj::PVal::Dict( List::Nil );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! odict {
  ( $dict:expr ) => {{
    let pval = obj::PVal::Dict( $dict );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! othunk {
  [ $body:expr ] => {{
    let pval = obj::PVal::OpenThunk( $body );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! olam {
  { $var:ident . $body:expr } => {{
    let pexp = obj::PExp::Lam(stringify!($var).to_string(), $body);
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
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
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
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
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }};
  { $var1:ident = $rhs1:expr , $( $var2:ident = $rhs2:expr ),+ ; $body:expr } => {{
    olet!($var1 = $rhs1 ; olet!( $( $var2 = $rhs2 ),+ ; $body ))
  }};
}

#[macro_export]
macro_rules! oproj {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Proj( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! oprim {
  ( $prim:expr ) => {{
    let pexp = obj::PExp::Prim( $prim );
    let exp  = obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top};
    let pval = obj::PVal::Thunk( adapton::collections::map_empty(), exp );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
}

#[macro_export]
macro_rules! ovarf {
  ( $var:ident ) => {{
    let v = ovar!($var);
    obj::Exp{pexp:Box::new(obj::PExp::Force(v)),
             cann:refl::CTyp::Top}
  }};
}

#[macro_export]
macro_rules! oref {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ref( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! oget {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Get( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! oset {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Set( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! oret {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ret( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

pub fn syn_tenv(store:&obj::Store, env:obj::Env) -> Option<refl::TEnv> {
  // TODO
  drop(store);
  panic!("list fold")
}

pub fn tenv_ext(store:&obj::Store, tenv:refl::TEnv, var:obj::Var, typ:refl::VTyp) -> refl::TEnv {
  drop(store);
  map_update(tenv, var, typ)
}

pub fn syn_exp(store:&obj::Store, tenv:refl::TEnv, exp:obj::Exp) -> Option<refl::CTyp> {
  syn_pexp(store, tenv, *exp.pexp)
}

pub fn chk_exp(store:&obj::Store, env:refl::TEnv, exp:obj::Exp, ctyp:refl::CTyp) -> bool {
  chk_pexp(store, env, *exp.pexp, ctyp)
}

pub fn syn_value(store:&obj::Store, tenv:refl::TEnv, value:obj::Val) -> Option<refl::VTyp> {
  syn_pvalue(store, tenv, *value.pval)
}

pub fn chk_value(store:&obj::Store, tenv:refl::TEnv, value:obj::Val, vtyp:refl::VTyp) -> bool {
  chk_pvalue(store, tenv, *value.pval, vtyp)
}

pub fn syn_pvalue(store:&obj::Store, tenv:refl::TEnv, value:obj::PVal) -> Option<refl::VTyp> {
  use refl::VTyp;
  use obj::PVal;
  match value {
    PVal::Thunk(env, e) => { 
      match syn_tenv(store, env) { 
        None => None,
        Some(tenv) => match syn_exp(store, tenv, e) {
          None => None,
          Some(c) => Some(VTyp::U(Box::new(c)))
        }}},
    PVal::OpenThunk(e) => { 
      match syn_exp(store, tenv, e) {
        None => None,
        Some(c) => Some(VTyp::U(Box::new(c)))
      }},
    PVal::Dict(d) => { match panic!("list fold") { None => None, Some(dt) => Some(VTyp::Dict(dt)) } }
    PVal::Num(_)  => Some(VTyp::Num),
    PVal::Str(_)  => Some(VTyp::Str),
    PVal::Loc(l)  => { match panic!("store lookup") { None => None, Some(dt) => Some(VTyp::Dict(dt)) } }
    _             => panic!(""),
  }
}

pub fn chk_pvalue(store:&obj::Store, tenv:refl::TEnv, value:obj::PVal, vtyp:refl::VTyp) -> bool {
  use refl::VTyp;
  use obj::PVal;
  match (vtyp, value) {
    (VTyp::U(c),     PVal::Thunk(env, e)) => { match syn_tenv(store, env) { None => false,
                                                                            Some(tenv) => chk_exp(store, tenv, e, *c) }},
    (VTyp::U(c),     PVal::OpenThunk(e))  => { chk_exp(store, tenv, e, *c)  },
    (VTyp::Dict(dt), PVal::Dict(d))       => panic!("list fold"),
    (VTyp::Num,      PVal::Num(_))        => true,
    (VTyp::Str,      PVal::Str(_))        => true,
    (VTyp::Ref(a),   PVal::Loc(l))        => panic!("store lookup"),
    (_,              _           )        => false,
  }
}

pub fn chk_pexp(store:&obj::Store, tenv:refl::TEnv, pexp:obj::PExp, ctyp:refl::CTyp) -> bool {
  use refl::{VTyp,CTyp};
  use obj::PExp;
  match (ctyp, pexp) {
    (c,              PExp::Force(v))     => chk_value(store, tenv, v, VTyp::U(Box::new(c))),
    (CTyp::F(a),     PExp::Ret(v))       => chk_value(store, tenv, v, *a),
    (CTyp::Arr(a,c), PExp::Lam(x,e))     => { let tenv = map_update(tenv, x, *a);
                                              chk_exp(store, tenv, e, *c)
    },
    (c,              PExp::App(e,v))     => { match syn_exp(store, tenv.clone(), e) 
                                              {
                                                Some(CTyp::Arr(a, c)) => chk_value(store, tenv, v, *a),
                                                _ => false,
                                              }
    },
    (CTyp::F(a),     PExp::Proj(v1, v2)) => { match syn_value(store, tenv.clone(), v1) 
                                                {
                                                  Some(VTyp::Dict(delta)) => { chk_value(store, tenv.clone(), v2, *a) },
                                                  _ => false,
                                                }
    },
    (c1,             PExp::Ann(e, c2))   => (c1 == c2),
    (CTyp::F(a),     PExp::Ref(v))       => chk_value(store, tenv, v, *a),
    (CTyp::F(a),     PExp::Get(v))       => chk_value(store, tenv, v, VTyp::Ref(a)),
    (CTyp::F(a),     PExp::Set(v1,v2))   => { match (syn_value(store, tenv.clone(), v1),
                                                     syn_value(store, tenv,         v2)) 
                                              {
                                                (Some(VTyp::Ref(a1)), Some(a2)) => { *a1 == a2 },
                                                _ => false,
                                              }
    },
    (c,              PExp::Let(x,e1,e2)) => { match syn_exp(store, tenv.clone(), e1) 
                                              {
                                                Some(CTyp::F(a)) => {
                                                  let tenv = map_update(tenv, x, *a);
                                                  chk_exp(store, tenv, e2, c)
                                                },
                                                _ => panic!("")
                                              }
    }
    _ => panic!(""),
  }
}

pub fn syn_pexp(store:&obj::Store, env:refl::TEnv, exp:obj::PExp) -> Option<refl::CTyp> {
  // TODO
  match exp {
    _ => panic!("")
  }
}
pub fn chk_stack(store:&obj::Store, stack:obj::Stack, typ:refl::CTyp) -> bool {
  use adapton::collections::*;
  if list_is_empty(&stack) { return false }
  else {
    let (frame, stack) = list_pop(stack) ;
    match (frame, typ) {
      (obj::Frame::App(v), 
       refl::CTyp::Arr(a,c)) => { 
        chk_value(store, list_nil(), v, *a) 
          && chk_stack(store, stack, *c) }
      (obj::Frame::Let(x,env,e) ,
       refl::CTyp::F(a)) => {
        match syn_tenv(store, env) { 
          None => false,
          Some(tenv) => {
            let tenv = tenv_ext(store, tenv, x, *a) ;
            match syn_exp(store, tenv, e) {
              None => false,
              Some(c) => chk_stack(store, stack, c)
            }
          }
        }
      }
      _ => false
    }
  }
}

pub fn chk_state(st:obj::State) -> Option<obj::State> {
  match syn_tenv(&st.store, st.env.clone()) {
    None => None,
    Some(tenv) => {
      match syn_pexp(&st.store, tenv, st.pexp.clone()) {
        None    => None,
        Some(c) => { 
          if chk_stack(&st.store, st.stack.clone(), c) { Some(st) }
          else { None }
        }
      }
    }
  }
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
  use adapton::collections::*;

  let env : obj::Env = map_empty();
  let env = map_update(env, "halt".to_string(),     oprim!(obj::Prim::Halt));
  let env = map_update(env, "openDb".to_string(),   oprim!(obj::Prim::DbOpen));
  let env = map_update(env, "filterDb".to_string(), oprim!(obj::Prim::DbFilter));
  let env = map_update(env, "joinDb".to_string(),   oprim!(obj::Prim::DbJoin));

  obj::State{store:map_empty(),
             nloc: 0,
             stack:List::Nil,
             env:  env,
             pexp: e}
}

pub fn small_step(st:obj::State) -> Result<obj::State, obj::State> {
  use obj::*;
  //use obj::PExp::*;
  use adapton::collections::*;

  if is_final(&st.pexp) {
    let st = match refl::do_pass (st) {
      None     => panic!("reflective layer chose to halt execution."),
      Some(st) => st,
    };
    if list_is_empty(&st.stack) { Err(st) }
    else {
      let (fr, stack) = list_pop(st.stack);
      match (fr, st.pexp) {
        (Frame::App(v), PExp::Lam(x,e)) => 
          Ok(State{env:list_push(st.env,(x,v)), stack:stack, pexp:*e.pexp, ..st}),
        (Frame::Let(x,fr_env,e), PExp::Ret(v)) => {
          let v = close_val(&st.env, v);
          Ok(State{env:list_push(fr_env,(x,v)), stack:stack, pexp:*e.pexp, ..st})
        },
        _ => panic!("invalid state: current stack and (final) expression do not match.")
      }}
  }
  else {
    let st = match st.pexp {
      PExp::Prim(prim) => {
        match prim {
          Prim::Halt => { return Err(State{pexp:PExp::Ret(ounit!()), ..st}) }
          Prim::DbOpen => {
            let (arg, stack) = {
              let (fr, stack) = list_pop(st.stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected an argument")
              }}; 
            // TODO: Create/Open a database here!
            State{stack:stack, pexp:PExp::Ret(ounit!()), ..st}
          }
          Prim::DbFilter => {
            let (arg1, stack) = {
              let (fr, stack) = list_pop(st.stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a first argument")
              }}; 
            let (arg2, stack) = {
              let (fr, stack) = list_pop(stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a second argument")
              }}; 
            // TODO: Create/Open a database here!
            State{stack:stack, pexp:PExp::Ret(ounit!()), ..st}
          }
          Prim::DbJoin => {
            let (arg, stack) = {
              let (fr, stack) = list_pop(st.stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a first argument")
              }}; 
            let (arg, stack) = {
              let (fr, stack) = list_pop(stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a second argument")
              }}; 
            let (arg, stack) = {
              let (fr, stack) = list_pop(stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a third argument")
              }}; 
            let (arg, stack) = {
              let (fr, stack) = list_pop(stack);              
              match fr {
                Frame::App(v) => (v, stack),
                _ => panic!("stuck: DbOpen expected a forth argument")
              }}; 
            // TODO: Create/Open a database here!
            State{stack:stack, pexp:PExp::Ret(ounit!()), ..st}
          }
          _ => unimplemented!()
        }
      }
      PExp::Ann(e,_) => { State{pexp:*e, ..st} }
      PExp::App(e, v) => {
        let stack = list_push(st.stack, Frame::App(close_val(&st.env, v)));
        State{stack:stack, pexp:*e.pexp, ..st}
      }
      PExp::Let(x,e1,e2) => {
        let stack = list_push(st.stack, Frame::Let(x,st.env.clone(),e2));
        State{stack:stack, pexp:*e1.pexp, ..st}
      }
      PExp::Force(v) => {
        match *close_val(&st.env,v).pval {
          PVal::Thunk(env,e) => State{env:env, pexp:*e.pexp, ..st},
          _ => panic!("stuck: forced a value that is not a thunk")
        }
      }      
      PExp::Ref(v) => {
        let v = close_val(&st.env,v) ;
        let store = <List<_> as MapIntro<_,_>>::update(st.store, st.nloc, v);
        State{nloc:st.nloc+1, store:store, pexp:PExp::Ret(oloc!(st.nloc)), ..st}
      }
      PExp::Set(v1,v2) => {
        let v1 = close_val(&st.env, v1);
        let v2 = close_val(&st.env, v2);
        match *v1.pval {
          PVal::Loc(loc) => {
            let store = <List<_> as MapIntro<_,_>>::update(st.store, loc, v2);
            State{store:store, pexp:PExp::Ret(ounit!()), ..st}
          }
          _ => panic!("stuck: ref-set on a non-location: {:?}", v1)
        }        
      }
      PExp::Get(v) => {
        let v = close_val(&st.env,v) ;
        match *v.pval {
          PVal::Loc(loc) => {          
            let w = <List<_> as MapElim<_,_>>::find(&st.store, &loc);
            match w {
              None => panic!("internal error: ref-get dereferenced non-existent store location"),
              Some(w) => State{pexp:PExp::Ret(w),.. st}
            }
          }
          _ => panic!("stuck: ref-get on a non-location: {:?}", v)
        }
      }      
      PExp::Proj(v1,v2) => {
        let v1 = close_val(&st.env,v1) ;
        let v2 = close_val(&st.env,v2) ;
        match *v1.pval {
          PVal::Dict(dict) => {          
            let w = <List<_> as MapElim<_,_>>::find(&dict, &v2);
            match w {
              None => panic!("stuck: dict-proj failed on projection of given value: {:?}", v2),
              Some(w) => State{pexp:PExp::Ret(w),.. st}
            }
          }
          _ => panic!("stuck: dict-proj on a non-dictionary: {:?}", v1)
        }
      }
      PExp::Ext(v1,v2,v3) => {
        let v1 = close_val(&st.env, v1);
        let v2 = close_val(&st.env, v2);
        let v3 = close_val(&st.env, v3);
        match *v1.pval {
          PVal::Dict(dict) => {
            let dict = <List<_> as MapIntro<_,_>>::update(dict, v2, v3);
            State{pexp:PExp::Ret(odict!(dict)), ..st}
          }
          _ => panic!("stuck: dict-ext on a non-dictionary: {:?}", v1)
        }
      }      
      // These are terminal cases, and thus are excluded in this match:
      PExp::Ret(_)   => unreachable!(),
      PExp::Lam(_,_) => unreachable!(),
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
