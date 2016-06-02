extern crate csv;

use std::fmt::Debug;
use std::fmt::Formatter;

//#[macro_use]
extern crate adapton;
use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
use std::rc::Rc;

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

  pub fn do_pass(st:super::obj::State) -> Option<super::obj::State> { 
    println!("do pass");
    super::chk_state(st) 
  }
}

impl Debug for obj::State {
  fn fmt(&self, f:&mut Formatter) -> std::fmt::Result { 
    write!(f, "{{\n\tstore:{:?},\n\tstack:{:?},\n\tenv:{:?},\n\tpexp:{:?}\n}}",
           self.store,
           self.stack,
           self.env,
           self.pexp)
  }
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
macro_rules! odb {
  [ ] => {{
    let pval = obj::PVal::Db( list_nil() ) ;
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }};
  ( $val1:expr, $vals:expr ) => {{
    match *($vals).pval {
      obj::PVal::Db( db ) => {
        obj::PVal::Db( list_cons( $val1, db ) )
      },
      _ => unreachable!()
    }
  }};
  [ $val1:expr , $( $vals:expr ),* ] => {{
    odb!( $val1, odb![ $( $vals ),* ] )
  }}
}

#[macro_export]
macro_rules! odict {
  [ ] => {{
    let pval = obj::PVal::Dict( map_empty() ) ;
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
  }}
  ;
  ( $val1:expr => $val2:expr , $val3:expr ) => {{
    match *($val3).pval {
      PVal::Dict( dict ) => {
        let dict = map_update( dict, $val1, $val2 );
        let pval = obj::PVal::Dict( dict );
        obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
      }
      _ => unreachable!()        
    }
  }};
  [ $val1:expr => $val2:expr , $( $val3:expr => $val4:expr ),* ] => {{
    odict!( $val1 => $val2, odict![ $( $val3 => $val4 ),* ] );
  }};
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
macro_rules! oann {
  { $lhs:expr ,?: $ctyp:expr } => {{
    let pe = obj::PExp::Ann($lhs.pexp, $ctyp) ;
    obj::Exp{pexp:Box::new(pe), cann:refl::CTyp::Top}
  }};
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
macro_rules! ohalt {
  ( ) => {{
    let pexp = obj::PExp::Prim(obj::Prim::Halt);
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

// #[macro_export]
// macro_rules! oprim {
//   ( $prim:expr ) => {{
//     let pexp = obj::PExp::Prim( $prim );
//     let exp  = obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top};
//     let pval = obj::PVal::Thunk( adapton::collections::map_empty(), exp );
//     obj::Val{pval:Box::new(pval), vann:refl::VTyp::Top}
//   }}
// }

#[macro_export]
macro_rules! oopendb {
  ( $v1:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbOpen( $v1 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! ofilterdb {
  ( $v1:expr, $v2:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbFilter( $v1, $v2 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! oeq {
  ( $v1:expr, $v2:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::Eq( $v1, $v2 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
  }}
}

#[macro_export]
macro_rules! ojoindb {
  ( $v1:expr, $v2:expr, $v3:expr, $v4:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbJoin($v1, $v2, $v3, $v4 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Top}
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

pub fn syn_tenv(store:&obj::Store, env:obj::Env) -> Option<(refl::TEnv, obj::Env)> {
  // perform a fold in the optional-(map,map) monad; None begets None;
  // Some((tenv, env)) leads to further checking and building of tenv and env
  let tenv0 : refl::TEnv = map_empty();
  let  env0 : obj::Env   = map_empty();
  map_fold 
    (env, Some((tenv0, env0)),
     Rc::new(move |x:String,v:obj::Val,envs:Option<(refl::TEnv, obj::Env)>| 
             match envs {
               None              => None,
               Some((tenv, env)) => {
                 match syn_value(store, tenv.clone(), v) {
                   None          => None,                   
                   Some((vt, v)) => Some( ( map_update(tenv, x.clone(), vt),
                                            map_update(env,  x,          v)) ),
                 }
               }
             }))
}

pub fn tenv_ext(store:&obj::Store, tenv:refl::TEnv, var:obj::Var, typ:refl::VTyp) -> refl::TEnv {
  drop(store);
  map_update(tenv, var, typ)
}

pub fn syn_exp(store:&obj::Store, tenv:refl::TEnv, exp:obj::Exp) -> Option<(refl::CTyp, obj::Exp)> {
  match syn_pexp(store, tenv, *exp.pexp) {
    None           => None,
    Some((ct, pe)) => Some((ct.clone(), obj::Exp{pexp:Box::new(pe), cann:ct})),
  }
}

pub fn chk_exp(store:&obj::Store, env:refl::TEnv, exp:obj::Exp, ctyp:refl::CTyp) -> Option<obj::Exp> {
  match chk_pexp(store, env, *exp.pexp, ctyp.clone()) {
    None => None,
    Some(pe) => Some(obj::Exp{pexp:Box::new(pe), cann:ctyp}),
  }
}

pub fn syn_value(store:&obj::Store, tenv:refl::TEnv, value:obj::Val) -> Option<(refl::VTyp, obj::Val)> {
  match syn_pvalue(store, tenv, *value.pval) {
    None           => None,
    Some((vt, pv)) => { Some((vt.clone(), obj::Val{pval:Box::new(pv), vann:vt})) },
  }
}

pub fn chk_value(store:&obj::Store, tenv:refl::TEnv, value:obj::Val, vtyp:refl::VTyp) -> Option<obj::Val> {
  match chk_pvalue(store, tenv, *value.pval, vtyp.clone()) {
    None     => None,
    Some(pv) => { Some(obj::Val{pval:Box::new(pv), vann:vtyp}) }
  }
}

pub fn syn_pvalue(store:&obj::Store, tenv:refl::TEnv, value:obj::PVal) -> Option<(refl::VTyp, obj::PVal)> {
  use refl::VTyp;
  use obj::PVal;
  match value {
    PVal::Var(x)  => { match map_find(&tenv, &x) {
      None     => None,
      Some(xt) => {
        Some((xt, PVal::Var(x)))
      }}}
    PVal::Num(n)  => Some((VTyp::Num, PVal::Num(n))),
    PVal::Str(s)  => Some((VTyp::Str, PVal::Str(s))),
    PVal::Loc(l)  => { match map_find(store, &l) { 
      None    => None, 
      Some(v) => {
        // use stored value's annotation; 
        // avoid traversing stored value v; avoids cycles.
        Some((v.vann, PVal::Loc(l)))
      }
    }}
    PVal::Db(db) => {
      if list_is_empty(&db) {
        let t = VTyp::Db(Box::new(VTyp::Dict(Box::new(list_nil()))));
        Some((t, PVal::Db(list_nil())))
      } else {
        let (d,db) = list_pop(db) ;
        match syn_value(store, tenv.clone(), d) {
          None => None,
          Some((dt, d)) => {
            let db_out = list_cons(d, list_nil());
            let out = list_fold(db, Some((dt, db_out)), Rc::new(|d,out|{
              match out {
                None => None,
                Some((dt, db)) => 
                  match syn_value(store, tenv.clone(), d) {
                    None => None,
                    Some((dt2, d)) => { 
                      if dt == dt2 { Some((dt, list_cons(d, db))) }
                      else { None }
                    }
                  }
              }
            }));
            match out {
              None           => None,
              Some((dt, db)) => Some((VTyp::Db(Box::new(dt)), PVal::Db(db)))
            }
          }
        }
      }
    }
    PVal::Dict(d) => { 
      let ds = {
        let d0  : obj::Dict  = map_empty() ;
        let dt0 : refl::Dict = map_empty() ;
        map_fold(d, Some((dt0, d0)),
                 Rc::new(|k,v,ds| {
                   match ds {
                     None => None,
                     Some((dt, d)) => {
                       let k : obj::Val = k ;
                       let v : obj::Val = v ;
                       match ( syn_value(store, tenv.clone(), k),
                               syn_value(store, tenv.clone(), v) 
                       ) {
                         (Some((kt, k)), Some((vt, v))) => { Some(
                           ( map_update(dt, k.clone(), vt),
                             map_update(d,  k,         v )
                           )
                         )}                          
                         _ => None,
                       }}}}))
        };
      match ds {
        None          => None,
        Some((dt, d)) => Some(( VTyp::Dict(Box::new(dt)), PVal::Dict(d) ))
      }
    }
    PVal::Thunk(env, e) => { 
      match syn_tenv(store, env) { 
        None              => None,
        Some((tenv, env)) => match syn_exp(store, tenv, e) {
          None         => None,
          Some((c, e)) => Some( (VTyp::U(Box::new(c)),
                                 PVal::Thunk(env, e)) )
        }}},
    
    pv => panic!("syn_pvalue {:?}", pv),
  }
}

pub fn chk_pvalue(store:&obj::Store, tenv:refl::TEnv, value:obj::PVal, vtyp:refl::VTyp) -> Option<obj::PVal> {
  use refl::VTyp;
  use obj::PVal;
  match (vtyp, value) {
    (VTyp::Str, PVal::Str(s)) => Some(PVal::Str(s)),
    (VTyp::Num, PVal::Num(n)) => Some(PVal::Num(n)),
    (VTyp::U(c), PVal::Thunk(env, e)) => { 
      match syn_tenv(store, env) 
      { 
        None => None,
        Some((tenv, env)) => {
          match chk_exp(store, tenv, e, *c) {
            None    => None,
            Some(e) => Some(PVal::Thunk(env, e))
          }
        }
      }
    }
    (VTyp::U(c), PVal::OpenThunk(e)) => { 
      match chk_exp(store, tenv, e, *c) {
        None => None,
        Some(e) => Some(PVal::OpenThunk(e))
      }        
    }
    // (VTyp::Dict(dt), PVal::Dict(d))       => { map_fold
    //                                            (d, true, Rc::new(|k:obj::Val,v:obj::Val,ret:bool| {
    //                                              if !ret { false } else { 
    //                                                let kt = syn_value(store, map_empty(), k.clone());
    //                                                let vt = syn_value(store, map_empty(), v);
    //                                                match (kt, vt) {
    //                                                  (Some(kt), Some(vt)) => match map_find(&*dt, &k) {
    //                                                    Some(kt2) => kt == kt2,
    //                                                    None => false,
    //                                                  },
    //                                                  _ => false,
    //                                                }}})) 
    // },
    // (VTyp::Ref(a),   PVal::Loc(l))        => { match map_find(store, &l) { 
    //   None    => false, 
    //   Some(v) => (v.vann == *a),
    // }}
    (vt, v)        => panic!("chk_pvalue {:?} {:?}", vt, v),
  }
}

pub fn chk_pexp(store:&obj::Store, tenv:refl::TEnv, pexp:obj::PExp, ctyp:refl::CTyp) -> Option<obj::PExp> {
  use refl::{VTyp,CTyp};
  use obj::PExp;
  println!("-- chk_pexp {:?}\n <== {:?}", pexp, ctyp);
  match (ctyp, pexp) {    
    // Lambda is checking mode
    (CTyp::Arr(a,c), PExp::Lam(x,e)) => { 
      let tenv = map_update(tenv, x.clone(), *a);
      match chk_exp(store, tenv, e, *c) {
        None => None,
        Some(e) => Some(PExp::Lam(x, e))
      }
    },
    // For other forms: 
    // Do synthesis and confirm that types match:
    (c, e) => {
      match syn_pexp(store, tenv, e) {
        None => None,
        Some((c2, e)) => {
          // XXX: Subsume rule
          if c == c2 { Some(e) }
          else { 
            println!("subsumption failed:\n\t{:?}\n <>\t{:?}", c, c2);
            None 
          }
        }
      }
    }
  }
}

  //   (c,              PExp::Force(v))     => chk_value(store, tenv, v, VTyp::U(Box::new(c))),
  //   (CTyp::F(a),     PExp::Ret(v))       => chk_value(store, tenv, v, *a),
  //   (CTyp::Arr(a,c), PExp::Lam(x,e))     => { let tenv = map_update(tenv, x, *a);
  //                                             chk_exp(store, tenv, e, *c)
  //   },
  //   (c,              PExp::App(e,v))     => { match syn_exp(store, tenv.clone(), e) 
  //                                             {
  //                                               Some(CTyp::Arr(a, c)) => chk_value(store, tenv, v, *a),
  //                                               _ => false,
  //                                             }
  //   },
  //   (CTyp::F(a),     PExp::Proj(v1, v2)) => { match syn_value(store, tenv.clone(), v1) 
  //                                               {
  //                                                 Some(VTyp::Dict(delta)) => { chk_value(store, tenv.clone(), v2, *a) },
  //                                                 _ => false,
  //                                               }
  //   },
  //   (c1,             PExp::Ann(e, c2))   => (c1 == c2),
  //   (CTyp::F(a),     PExp::Ref(v))       => chk_value(store, tenv, v, *a),
  //   (CTyp::F(a),     PExp::Get(v))       => chk_value(store, tenv, v, VTyp::Ref(a)),
  //   (CTyp::F(a),     PExp::Set(v1,v2))   => { match (syn_value(store, tenv.clone(), v1),
  //                                                    syn_value(store, tenv,         v2)) 
  //                                             {
  //                                               (Some(VTyp::Ref(a1)), Some(a2)) => { *a1 == a2 },
  //                                               _ => false,
  //                                             }
  //   },
  //   (c,              PExp::Let(x,e1,e2)) => { match syn_exp(store, tenv.clone(), e1) 
  //                                             {
  //                                               Some(CTyp::F(a)) => {
  //                                                 let tenv = map_update(tenv, x, *a);
  //                                                 chk_exp(store, tenv, e2, c)
  //                                               },
  //                                               _ => false,
  //                                             }
  //   }
  //   _ => panic!(""),
  // }


pub fn syn_pexp(store:&obj::Store, tenv:refl::TEnv, exp:obj::PExp) -> Option<(refl::CTyp, obj::PExp)> {
  use obj::PExp;
  use obj::Prim;
  use refl::CTyp;
  use refl::VTyp;
  println!("-- syn_pexp {:?}", exp);
  match exp {
    PExp::Ret(v) => { 
    match syn_value(store, tenv, v) {
      None          => None,
      Some((vt, v)) => Some( (refl::CTyp::F(Box::new(vt)), 
                              obj::PExp::Ret(v)) )
    }},    
    PExp::Ann(e, et) => {
      match chk_pexp(store, tenv, *e, et.clone()) {
        None    => None,
        Some(e) => Some((et, e))
      }
    }
    PExp::Prim(Prim::Halt) => { 
      Some((CTyp::Top, PExp::Prim(Prim::Halt))) 
    }
    PExp::Prim(Prim::Eq(v1, v2)) => {
      match (syn_value(store, tenv.clone(), v1),
             syn_value(store, tenv,         v2)) {
        (Some((v1t, v1)), Some((v2t, v2))) => {
          Some((CTyp::F( Box::new( VTyp::Bool ) ),
                PExp::Prim(Prim::Eq(v1, v2))))
        }
        _ => None
      }      
    },
    PExp::Prim(Prim::DbOpen(v)) => {
      match chk_value(store, tenv, v, refl::VTyp::Str) {
        None => None,
        Some(v) => {
          Some(( CTyp::F(Box::new(VTyp::Db(Box::new(VTyp::Top)))), 
                 PExp::Prim(Prim::DbOpen(v) )))
        },
      }
    },
    PExp::Prim(Prim::DbFilter(v1, v2)) => {
      match syn_value(store, tenv.clone(), v1) {
        None => None,
        Some(( VTyp::Db( a ), v1 )) => {
          let f_bool = CTyp::F( Box::new(VTyp::Bool ) );
          let f_db   = CTyp::F( Box::new(VTyp::Db(a.clone())) ) ;
          match chk_value( store, tenv, v2, 
                           VTyp::U(Box::new(CTyp::Arr(a, Box::new( f_bool ) ))) ) {            
            None => None,
            Some(v2) => {
              Some(( f_db, PExp::Prim(Prim::DbFilter(v1, v2)) ))
            }
          }
        },
        x => { println!("DbFilter: first param should be a database, not {:?}", x) ; None },
      }
    },
    PExp::Prim(Prim::DbJoin(v1, v2, v3, v4)) => {
      match  (syn_value(store, tenv.clone(), v1),
              syn_value(store, tenv.clone(), v2),
              syn_value(store, tenv.clone(), v3),
              syn_value(store, tenv.clone(), v4)) {
        ( Some((v1t, v1)), Some((v2t, v2)), 
          Some((v3t, v3)), Some((v4t, v4)) ) => {          
          match(v1t, v3t) {
            (VTyp::Db(ref a), VTyp::Db(ref b)) if **a == VTyp::Top && **b == VTyp::Top => {
              let f_db = CTyp::F( Box::new(VTyp::Db( Box::new(VTyp::Top) )) ) ;
              Some(( f_db, PExp::Prim(Prim::DbJoin(v1, v2, v3, v4)) ))
            },
            (VTyp::Db(a), VTyp::Db(b)) => {
              panic!("")
            },
            _ => None,
          }
        },
        _ => None,
      }
    },
    PExp::Let(x,e1,e2) => {
      match syn_exp(store, tenv.clone(), e1) {
        None => None,
        Some((CTyp::F(a), e1)) => {
          let tenv = map_update(tenv, x.clone(), *a) ;
          match syn_exp(store, tenv, e2) {
            None => None,            
            Some((c, e2)) => {
              Some((c, PExp::Let(x,e1,e2)))
            }
          }
        },
        _ => None,
      }},      
    PExp::App(e,v) => {
      match syn_exp(store, tenv.clone(), e) {
        None => None,
        Some((CTyp::Arr(a, c), e)) => {
          match chk_value(store, map_empty(), v, *a) {
            None => None,
            Some(v) => {
              Some((*c, PExp::App(e, v)))
            }
          }
        },
        _ => None,
      }
    },
    PExp::Force(v) => {
      match syn_value(store, tenv, v) {
        None => None,
        Some((VTyp::U(c), v)) => {
          Some((*c, PExp::Force(v)))
        },
        _ => None,
      }
    }
    PExp::Proj(v1, v2) => {
      match syn_value(store, tenv.clone(), v1) {
        None => None,
        Some((VTyp::Top, v1)) => {
          match syn_value(store, tenv, v2) {
            None => None,
            Some((v2t, v2)) => {
              Some((CTyp::F(Box::new(VTyp::Top)), // imprecise
                    PExp::Proj(v1, v2)))                  
            }
          }          
        },
        Some((VTyp::Dict(delta), v1)) => {
          match syn_value(store, tenv, v2) {
            None => None,
            Some((v2t, v2)) => {
              match map_find(&*delta, &v2) {
                None      => { println!("syn_pvalue: Proj: field {:?}\n\tnot in type {:?}", v2, delta); None},
                Some(v3t) => Some((CTyp::F(Box::new(v3t)), // precise
                                   PExp::Proj(v1, v2)))                  
              }
            }
          }
        },
        _ => None,
      }

    }
    pe => panic!("syn_pexp {:?}", pe)
  }
}
pub fn chk_stack(store:&obj::Store, stack:obj::Stack, typ:refl::CTyp) -> Option<obj::Stack> {
  use adapton::collections::*;
  if list_is_empty(&stack) { return Some(list_nil()) }
  else {
    let (frame, stack) = list_pop(stack) ;
    match (frame, typ) {
      (obj::Frame::App(v), 
       refl::CTyp::Arr(a,c)) => { 
        match ( chk_value(store, list_nil(), v, *a), 
                chk_stack(store, stack, *c) ) {
          (Some(v), Some(stack)) => Some(list_cons(obj::Frame::App(v), stack)),
          _                      => None,
        }},
      (obj::Frame::Let(x,env,e) ,
       refl::CTyp::F(a)) => {
        match syn_tenv(store, env) { 
          None => None,
          Some((tenv, env)) => {
            let tenv = tenv_ext(store, tenv, x.clone(), *a) ;
            match syn_exp(store, tenv, e) {
              None => None,
              Some((et, e)) => match chk_stack(store, stack, et) {
                None => None,
                Some(stack) => {
                  Some(list_cons(obj::Frame::Let(x,env,e), stack))
                }
              }
            }
          }
        }
      }
      _ => None
    }
  }
}

pub fn chk_state(st:obj::State) -> Option<obj::State> {
  let store0 = st.store.clone();
  let store  = 
    map_fold(st.store, Some(map_empty()),
             Rc::new(|l:obj::Loc, v:obj::Val, store:Option<obj::Store>|
                     match store {
                       None => None,
                       Some(store) => {
                         match syn_value(&store0, map_empty(), v) {
                           Some((_, vt)) => Some(map_update(store, l, vt)),
                           None          => None,
                         }}}));  
  match store {
    None => None,
    Some(store) => {
      match syn_tenv(&store, st.env) {
        None => None,
        Some((tenv, env)) => {
          match syn_pexp(&store, tenv, st.pexp) {
            None            => None,
            Some((c, pexp)) => { 
              match chk_stack(&store, st.stack, c) {
                None        => None,
                Some(stack) => {
                  Some(obj::State{
                    store:store,
                    stack:stack,
                    env:  env,
                    pexp: pexp,
                    ..st
                  })
                }}}}}}}}
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
    Db(db0) => {
      let db : obj::Db = list_nil();
      let db = list_fold(db0, db, Rc::new(|v,db| list_cons(close_val(env, v), db)));
      Db(db)
    }
    OpenThunk(e)  => Thunk(env.clone(), e),
    Thunk(env2,e) => Thunk(env2,e),
    Dict(List::Nil) => Dict(List::Nil),
    Dict(dict0)    => {
      let dict : obj::Dict = map_empty();
      let dict = map_fold(dict0, dict, Rc::new(|x,v,map| map_update(map,x,close_val(env,v))));
      Dict(dict)
    },
    Num(n)        => Num(n),
    Str(s)        => Str(s),
    Loc(l)        => Loc(l),
    Var(x)        => match map_find(env, &x) {
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
  //let env = map_update(env, "halt".to_string(),     oprim!(obj::Prim::Halt));
  //let env = map_update(env, "openDb".to_string(),   oprim!(obj::Prim::DbOpen));
  //let env = map_update(env, "filterDb".to_string(), oprim!(obj::Prim::DbFilter));
  //let env = map_update(env, "joinDb".to_string(),   oprim!(obj::Prim::DbJoin));

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
  let st = match refl::do_pass (st.clone()) {
    None     => { println!("!!!\t--/--> reflective layer chose to halt execution."); st }
    Some(st) => st,
  };  
  if is_final(&st.pexp) {
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
          Prim::Eq(v1, v2) => {
            // TODO: 
            State{pexp:PExp::Ret(ounit!()), ..st}
          }
          Prim::DbOpen(v) => {
            let authors_csv = odb![ ];
            let books_csv = odb![ ];            
            //   odb![ odict![ ostr!("name") => ostr!("name1"), ostr!("citizenship") => ostr!("US") ],
            //         odict![ ostr!("name") => ostr!("name2"), ostr!("citizenship") => ostr!("not US") ],
            //         odict![ ostr!("name") => ostr!("name3"), ostr!("citizenship") => ostr!("US") ] 
            //   ];
            // let books_csv = 
            //   odb![ odict![ ostr!("author") => ostr!("name1"), ostr!("title") => ostr!("title1") ],
            //         odict![ ostr!("author") => ostr!("name2"), ostr!("title") => ostr!("title2") ],
            //         odict![ ostr!("author") => ostr!("name3"), ostr!("title") => ostr!("title3") ] 
            //   ];            
            let db = match *close_val(&st.env, v).pval {
              PVal::Str(s) => {
                if      s == "authors.csv" { authors_csv }
                else if s == "books.csv"   { books_csv   }
                else {  panic!("stuck: don't know that database") }
              },
              _ => panic!("stuck: dont know how to open that database")
            };
            // TODO: XXX: Return a database here! (either author or book)
            State{pexp:PExp::Ret(db), ..st}
          }
          Prim::DbFilter(v1, v2) => {
            let v1 = close_val(&st.env, v1);
            let v2 = close_val(&st.env, v2);
            // XXX: TODO: Actually do the filtering step
            State{pexp:PExp::Ret(v1), ..st}
          }
          Prim::DbJoin(v1, v2, v3, v4) => {
            // TODO:
            State{pexp:PExp::Ret(ounit!()), ..st}
          }
        }
      }
      PExp::Ann(e,_) => { State{pexp:*e, ..st} } // TODO: Check the annotation?
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
fn test_listing_1_ver_a() { listing_1_ver_a() }

#[test]
fn test_listing_1_ver_b() { listing_1_ver_b() }

fn listing_1_ver_a() {
  let vty_authbks_us : refl::VTyp = { 
    let dict : refl::Dict = map_empty();
    let dict = map_update( dict, ostr!("name"),        refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("author"),      refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("citizenship"), refl::VTyp::Str ) ;
    refl::VTyp::Db( Box::new(refl::VTyp::Dict( Box::new( dict ) ) ) ) } ;
  
  let example : obj::Exp =
    olet!{ authors    = oopendb!( ostr!("authors.csv") ),
           authorsUS  = ofilterdb!(
             ovar!(authors),
             othunk![ olam!(author.
                            olet!{c = oproj!(ovar!(author), ostr!("citizenship")) ;
                                  oeq!(ovar!(c), ostr!("US"))}
             )]),
           books      = oopendb!( ostr!("books.csv") ),
           authbksUS  = ojoindb!( ovar!(authorsUS), ostr!("name"),
                                  ovar!(books),     ostr!("author") )
           ;
           ohalt!()
    };
  let st = initial_state(*example.pexp);
  drop(eval(st));
}

fn listing_1_ver_b() {
  let vty_authbks_us : refl::VTyp = { 
    let dict : refl::Dict = map_empty();
    let dict = map_update( dict, ostr!("name"),        refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("author"),      refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("citizenship"), refl::VTyp::Str ) ;
    refl::VTyp::Db( Box::new(refl::VTyp::Dict( Box::new( dict ) ) ) ) } ;
  
  let example : obj::Exp =
    olet!{ authors    = oopendb!(ostr!("authors.csv")),
           authorsUS  = ofilterdb!(
             ovar!(authors),
             othunk![ olam!(author.
                            olet!{c = oproj!(ovar!(author), ostr!("citizenship")) ;
                                  oeq!(ovar!(c), ostr!("US"))}
             )]),
           books      = oopendb!(ostr!("books.csv")),
           authbksUS  = ojoindb!( ovar!(authorsUS), ostr!("name"),
                                  ovar!(books),     ostr!("author") ),
           authbksUS2 = oann!( oret!(ovar!(authbksUS)),
                              ?: refl::CTyp::F(Box::new(vty_authbks_us)) ) // Check that authbksUS has a particular (database) type
           ;
           ohalt!()
    };
  let st = initial_state(*example.pexp);
  drop(eval(st));
}

fn main() {
  //use obj::*;
  listing_1_ver_a()
}
