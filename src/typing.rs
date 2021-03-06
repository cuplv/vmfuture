use syntax::refl;
use syntax::obj;

//#[macro_use]
use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
use std::rc::Rc;

pub fn vtyp_consis(vtyp1:refl::VTyp, vtyp2:refl::VTyp) -> bool {
  use syntax::refl::VTyp::*;
  match (vtyp1, vtyp2) {
    (Top, _) => true,
    (_, Top) => true,
    (Num, Num) => true,
    (Str, Str) => true,
    (Bool,Bool) => true,
    (Dict(d1), Dict(d2)) => {
      map_fold(*d1.clone(), true, 
               Rc::new(|v1:obj::Val, a1, ok:bool| 
                       if !ok { false } else {
                         match map_find(&*d2, &v1) {
                           None     => { println!("d2:{:?}\ndoes not map v1:{:?}", d2, v1) ; false},
                           Some(a2) => vtyp_consis(a1, a2),                             
                         }}))
        &&
        map_fold(*d2, true, 
                 Rc::new(|v2, a2, ok:bool| 
                         if !ok { false } else { 
                           match map_find(&*d1, &v2) {
                             None     => { println!("{:?} {:?}", d1, v2) ; false},
                             Some(a1) => vtyp_consis(a1, a2),
                           }}))        
    },
    (Db(vt1),  Db(vt2))  => vtyp_consis(*vt1, *vt2),
    (Ref(vt1), Ref(vt2)) => vtyp_consis(*vt1, *vt2),
    (U(c1),    U(c2))    => ctyp_consis(*c1, *c2),
    _ => false,
  }
}

pub fn ctyp_consis(ctyp1:refl::CTyp, ctyp2:refl::CTyp) -> bool {
  use syntax::refl::CTyp::*;
  match (ctyp1, ctyp2) {
    (Top, _  ) => true,
    (_  , Top) => true,
    (F(a), F(b)) => vtyp_consis(*a, *b),
    (Arr(a,c), Arr(b,d)) => vtyp_consis(*a, *b) && ctyp_consis(*c,*d),
    _ => false,      
  }  
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
  use syntax::refl::VTyp;
  use syntax::obj::PVal;
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
                       match ( syn_value(store, tenv.clone(), k.clone()),
                               syn_value(store, tenv.clone(), v) 
                       ) {
                         (Some((_kt, k)), Some((vt, v))) => { Some(
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
  use syntax::refl::VTyp;
  use syntax::obj::PVal;
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
  use syntax::refl::{CTyp};
  use syntax::obj::PExp;
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
    // Do synthesis and confirm that types "match", using some equiv relation:
    (c, e) => {
      match syn_pexp(store, tenv, e) {
        None => None,
        Some((c2, e)) => {
          // XXX: Subsume rule: 
          // Q: What's the right relation to enforce here?
          if ctyp_consis(c.clone(), c2.clone()) { Some(e) }
          else { 
            println!("subsumption failed:\n\t{:?}\n <not-consis>\t{:?}", c, c2);
            None 
          }
        }
      }
    }
  }
}

pub fn syn_pexp(store:&obj::Store, tenv:refl::TEnv, exp:obj::PExp) -> Option<(refl::CTyp, obj::PExp)> {
  use syntax::obj::PExp;
  use syntax::obj::Prim;
  use syntax::refl::CTyp;
  use syntax::refl::VTyp;
  println!("-- syn_pexp {:?}", exp);
  println!("   tenv: {:?}", tenv);
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
        Some(e) => Some((et.clone(), PExp::Ann(Box::new(e), et)))
      }
    }
    PExp::Prim(Prim::Halt) => { 
      Some((CTyp::Top, PExp::Prim(Prim::Halt))) 
    }
    PExp::Prim(Prim::Eq(v1, v2)) => {
      match (syn_value(store, tenv.clone(), v1),
             syn_value(store, tenv,         v2)) {
        (Some((_v1t, v1)), Some((_v2t, v2))) => {
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
        ( Some((v1t, v1)), Some((_v2t, v2)), 
          Some((v3t, v3)), Some((_v4t, v4)) ) => {          
          match(v1t.clone(), v3t.clone()) {
            (VTyp::Db(ref a), VTyp::Db(ref b)) if **a == VTyp::Top || **b == VTyp::Top => {
              let f_db = CTyp::F( Box::new(VTyp::Db( Box::new(VTyp::Top) )) ) ;
              Some(( f_db, PExp::Prim(Prim::DbJoin(v1, v2, v3, v4)) ))
            },
            (VTyp::Db(a), VTyp::Db(b)) => {
              match (*a.clone(),*b.clone()) {
                (VTyp::Dict(d1), VTyp::Dict(d2)) => {
                  match (map_find(&*d1, &v2), map_find(&*d2, &v4)) {
                    (Some(a12), Some(a24)) => {
                      if vtyp_consis(a12.clone(), a24.clone()) {
                        let dict = list_append( *d1, *d2 );
                        let f_db = CTyp::F( Box::new(VTyp::Db( Box::new(VTyp::Dict( Box::new( dict ) ) ) )) ) ;                          
                        Some(( f_db, PExp::Prim(Prim::DbJoin(v1, v2, v3, v4)) ))
                      }
                      else { 
                        println!("{:?}\n\t<not-consis> {:?}", a12, a24);
                        None 
                      }
                    },
                    finds => {
                      println!("one or more `map_find`s failed on dictionary types: {:?}", finds);
                      None},
                  }
                },               
                _ => {
                  println!("joinDb with non-dict databases: {:?}\n{:?}", a, b);
                  None
                },
              }
            },
            _ => {
              println!("joinDb with non databases: {:?}\n{:?}", v1t, v3t);
              None
            },
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
            Some((_v2t, v2)) => {
              Some((CTyp::F(Box::new(VTyp::Top)), // imprecise
                    PExp::Proj(v1, v2)))                  
            }
          }          
        },
        // TODO: Add case where value of v1 is unknown (could be a variable)
        //
        Some((VTyp::Dict(delta), v1)) => {
          match syn_value(store, tenv, v2) {
            None => None,
            Some((_v2t, v2)) => {
              match map_find(&*delta, &v2) {
                None      => { println!("syn_pvalue: Proj: field {:?}\n\tnot in type {:?}", v2, delta); None},
                Some(v3t) => Some((CTyp::F(Box::new(v3t)), // precise
                                   PExp::Proj(v1, v2)))                  
              }
            }
          }
        },
        Some((vt, v)) => {
          println!("expected a record, instead found {:?} => {:?}", v, vt);
          None
        },
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
