/*
JPW comments/understanding
example : obj::Exp
  //create initial state w/empty stack/store/env, but the given pexp
  let st = dynamics::initial_state(*example.pexp);
  //first do_pass: calls typing::chk_state(st)
  let st = dynamics::eval(st);
  let y2 = map_find(&st.env, &"y2".to_string());
  assert!( y2 == Some(ostr!("banana")) )
  
  
  
  Code qs:
  why the exp wrapping pexp/val wrapping pval pattern in typing.rs (nvm it's annotations)
  why pub vann:super::refl::VAnn =   pub type VAnn = VTyp; (ditto CAnn/CTyp)
  CTyp? continuation type? what is Arr, F, Unk
  
  Impl qs:
  extend syn_pexp, syn_pvalue, chk_pvalue, chk_pexp?
*/

extern crate adapton;

mod syntax;

#[macro_use]
mod macros;

mod typing;
mod dynamics;

use syntax::{obj,refl};
use adapton::collections::*;

//#[test]
#[allow(dead_code)]
fn test_store() {  
  let example : obj::Exp =
    olet!{ x  = oref!(ostr!("apple")),
           y1 = oget!(ovar!(x)),
           z  = oset!(ovar!(x), ostr!("banana")),
           y2 = oget!(ovar!(x))
           ;
           oret!(ovar!(y2))
    };
  let st = dynamics::initial_state(*example.pexp);
  let st = dynamics::eval(st);
  let y2 = map_find(&st.env, &"y2".to_string());
  assert!( y2 == Some(ostr!("banana")) )  
}

#[test]
fn test_listing_1_ver_a() { listing_1_ver_a() }

#[test]
fn test_listing_1_ver_b() { listing_1_ver_b() }

#[allow(dead_code)]
fn listing_1_ver_a() {
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
  let st = dynamics::initial_state(*example.pexp);
  drop(dynamics::eval(st));
}

#[allow(dead_code)]
fn listing_1_ver_b() {
  let vty_authbks_us : refl::VTyp = { 
    let dict : refl::Dict = map_empty();
    let dict = map_update( dict, ostr!("name"),        refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("author"),      refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("citizenship"), refl::VTyp::Str ) ;
    let dict = map_update( dict, ostr!("title"),       refl::VTyp::Str ) ;
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
                               // Annotation checks that authbksUS has a particular (database) type:
                               ?: refl::CTyp::F(Box::new(vty_authbks_us)) ) 
           ;
           ohalt!()
    };
  let st = dynamics::initial_state(*example.pexp);
  drop(dynamics::eval(st));
}

fn main() {
  //use obj::*;
  listing_1_ver_a()
}
