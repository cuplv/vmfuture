/* Sum_type_extension TODOs:
Verify correctness of close_pval implementation (dynamics)
Write working testcase and submit pull request

directions:
extending sum types to be n-ary (dicts are n-ary products?)
ML-style recursion (encoding into sum types?)
Unit type = empty Dict?
clean up the syntax v_v
desugar recursive constructors into helper functions?

Go through typechecker code and figure out what Rust things are being used
To figure out what needs to be reached


Pattern matching
Boolean algebra
map_fold/maps
Recursion
basic list ops

recursion:
ua.T -> T[ua.T/a] seems to be standard roll/unroll
iso vs. equirecursive?
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

#[test]
fn test_sum_type_extension_1() { sum_type_extension_1() }

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

#[allow(dead_code)]
fn sum_type_extension_1() {
	let example : obj::Exp = 
		olet!{ 	caseEx	= oret!(obj::Val{pval:Box::new(obj::PVal::Inj1(ostr!("hi"))), 
										 vann:refl::VTyp::Sum(Box::new(refl::VTyp::Str), Box::new(refl::VTyp::Str))});
				ohalt!()	};
		let st = dynamics::initial_state(*example.pexp);
		drop(dynamics::eval(st));
}

fn main() {
  //use obj::*;
  listing_1_ver_a()
}
