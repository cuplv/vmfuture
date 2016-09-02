extern crate csv;

use std::fmt::{Debug,Formatter,Result};
//use std::fmt::Result;

//#[macro_use]
//use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
//use std::rc::Rc;

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
  #[derive(PartialEq,Eq,Hash,Clone)]
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
    /// Computation Annotation, to be confirmed via OVV by the
    /// reflective layer, or else checked dynamically, upon completion
    /// of a terminal computation (when this frame is popped).
    Ann(super::refl::CAnn)
  }

  /// Primitives
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum Prim {
    Halt,
    DbOpen(Val),
    DbFilter(Val,Val),
    DbJoin(Val,Val,Val,Val),
    Eq(Val,Val),
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
    Db(Db),
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
  pub type Db   = List<Val>;
  //pub type Env  = List<(Var,Val)>;
  //pub type Dict = HashMap<Val,Val>;
  //pub type Env  = HashMap<Var,Val>;
}


#[allow(dead_code)]
pub mod refl {
  //use std::collections::HashMap;
  use adapton::collections::{List};
  
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum CTyp {
    Unk, 
    F(Box<VTyp>), // Ret
    Arr(Box<VTyp>, Box<CTyp>), // ->
  }
  #[derive(Debug,PartialEq,Eq,Hash,Clone)]
  pub enum VTyp {
    Unk,
    Num, Str, Bool,
    Dict(Box<Dict>),
    Db(Box<VTyp>), // "Database" (A multiset of some kind)
    Ref(Box<VTyp>),
    U(Box<CTyp>), // Thunk
  }
  //pub type Dict = HashMap<super::obj::Val,Typ>;
  pub type Dict = List<(super::obj::Val, VTyp)>;
  pub type VAnn = VTyp;
  pub type CAnn = CTyp;
  pub type TEnv = List<(super::obj::Var, VTyp)>;
}

impl Debug for obj::State {
  fn fmt(&self, f:&mut Formatter) -> Result { 
    write!(f, "{{\n\tstore:{:?},\n\tstack:{:?},\n\tenv:{:?},\n\tpexp:{:?}\n}}",
           self.store,
           self.stack,
           self.env,
           self.pexp)
  }
}
