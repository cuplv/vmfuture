//mod macros;
//mod syntax;
//mod typing;

//use macros;
use syntax::{obj,refl};
use typing;

//#[macro_use]
use adapton::collections::*;
//use adapton::engine::*;
//use adapton::macros::*;
use std::rc::Rc;

pub fn do_pass(st:obj::State) -> Option<obj::State> { 
  println!("do pass");
  typing::chk_state(st) 
}

pub fn is_final(exp:&obj::PExp) -> bool {
  match *exp {
    obj::PExp::Ret(_)   => true,
    obj::PExp::Lam(_,_) => true,
    _ => false,
  }
}

pub fn close_pval(env:&obj::Env, v:obj::PVal) -> obj::PVal {
	//TODO: implement close_pval for Inj1/Inj2
  use syntax::obj::PVal::*;
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
    },
    Inj1(v)       => Inj1(close_val(env, v)),
    Inj2(v)       => Inj2(close_val(env, v)),
  }
}

pub fn close_val(env:&obj::Env, v:obj::Val) -> obj::Val {
  obj::Val{pval:Box::new(close_pval(env, *v.pval)), ..v}
}

pub fn initial_state(e:obj::PExp) -> obj::State {
  use adapton::collections::*;
  obj::State{store:map_empty(),
             nloc: 0,
             stack:list_nil(),
             env:  map_empty(),
             pexp: e}
}

pub fn small_step(st:obj::State) -> Result<obj::State, obj::State> {
  use syntax::obj::*;
  //use obj::PExp::*;
  use adapton::collections::*;  
  let st = match do_pass (st.clone()) {
    None => { 
      panic!("!!!\t--/--> reflective layer chose to halt execution."); 
      //st 
    }
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
    	//TODO: implement for Case. Just switch exp to a Let for case 1 or 2 depending on Inj1/Inj2?
      PExp::Prim(prim) => {
        match prim {
          Prim::Halt => { return Err(State{pexp:PExp::Ret(ounit!()), ..st}) }
          Prim::Eq(_v1, _v2) => {
            // TODO: 
            State{pexp:PExp::Ret(ounit!()), ..st}
          }
          Prim::DbOpen(v) => {
            let authors_csv = {
              let auth1 = odict![ ostr!("name")        => ostr!("name1"),
                                  ostr!("citizenship") => ostr!("US")
              ];
              let auth2 = odict![ ostr!("name")        => ostr!("name2"),
                                  ostr!("citizenship") => ostr!("not-US")
              ];
              let auth3 = odict![ ostr!("name")        => ostr!("name3"),
                                  ostr!("citizenship") => ostr!("US")
              ];
              odb![ auth1, auth2, auth3 ]
            };
            let books_csv = {
              let book1 = odict![ ostr!("author") => ostr!("name1"),
                                  ostr!("title")  => ostr!("title1")
              ];
              let book2 = odict![ ostr!("author") => ostr!("name1"),
                                  ostr!("title")  => ostr!("title1")
              ];
              let book3 = odict![ ostr!("author") => ostr!("name1"),
                                  ostr!("title")  => ostr!("title1")
              ];
              odb![ book1, book2, book3 ]
            };
            let db = match *close_val(&st.env, v).pval {
              PVal::Str(s) => {
                if      s == "authors.csv" { authors_csv }
                else if s == "books.csv"   { books_csv }
                else {  panic!("stuck: don't know that database") }
              },
              _ => panic!("stuck: dont know how to open that database")
            };
            State{pexp:PExp::Ret(db), ..st}
          }
          Prim::DbFilter(v1, v2) => {
            let v1 = close_val(&st.env, v1);
            let _v2 = close_val(&st.env, v2);
            // XXX: TODO: Actually do the filtering step
            State{pexp:PExp::Ret(v1), ..st}
          }
          Prim::DbJoin(v1, v2, v3, v4) => {
            let v1 = close_val(&st.env, v1);
            let v2 = close_val(&st.env, v2);
            let v3 = close_val(&st.env, v3);
            let v4 = close_val(&st.env, v4);
            match (*v1.clone().pval, *v3.pval) {
              (PVal::Db(db1), PVal::Db(db3)) => {
                let out : obj::Db = list_nil();
                let out = 
                  list_fold
                  (db1, out, Rc::new(|r1:obj::Val,out|{
                    list_fold
                      (db3.clone(), out, Rc::new(|r3:obj::Val,out|{
                        let r1 = match *r1.clone().pval { PVal::Dict(r) => r, _ => panic!( "db should contain dicts") } ;
                        let r3 = match *r3.clone().pval { PVal::Dict(r) => r, _ => panic!( "db should contain dicts") } ;
                        match (map_find(&r1, &v2), map_find(&r3, &v4)) {
                          (Some(v1),Some(v3)) => {
                            if v1 == v3 { list_cons(odict![[ list_append(r1, r3) ]], out) }
                            else { out }
                          },
                          _ => out
                        }
                      }))
                   })) ;
                State{pexp:PExp::Ret(odb![[out]]), ..st}
              }
              _ => panic!("stuck: cannot join non-databases")
            }            
          }
        }
      }
      PExp::Ann(e,_) => { State{pexp:*e, ..st} } // XXX: TODO: Actually check the annotation!
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
            State{pexp:PExp::Ret(odict![[dict]]), ..st}
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

pub fn eval (st:obj::State) -> obj::State {
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

