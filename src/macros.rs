
#[macro_export]
macro_rules! ovar {
  ( $var:ident ) => {{
    obj::Val{pval:Box::new(obj::PVal::Var(stringify!($var).to_string())),
             vann:refl::VTyp::Unk}
  }};
}

#[macro_export]
macro_rules! ostr {
  ( $str:expr ) => {{
    let pval = obj::PVal::Str( $str.to_string() );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Str}
  }}
}

#[macro_export]
macro_rules! oloc {
  ( $loc:expr ) => {{
    let pval = obj::PVal::Loc( $loc );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }}
}

#[macro_export]
macro_rules! ounit {
  ( ) => {{
    let pval = obj::PVal::Dict( List::Nil );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }}
}

#[macro_export]
macro_rules! odb {
  [[ $vals:expr ]] => {{
    let pval = obj::PVal::Db( $vals );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }};
  [ $( $vals:expr ),* ] => {{
    let v = vec![ $( NameElse::Else( ( $vals ) ) ),* ];
    let l : List<_> = list_of_vec( &v );
    let pval = obj::PVal::Db( l );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }}
}

#[macro_export]
macro_rules! odict {
  [[ $val:expr ]] => {{
    let pval = obj::PVal::Dict( $val ) ;
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}  
  }};  
  [ ] => {{
    let pval = obj::PVal::Dict( list_nil() ) ;
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}  
  }};  
  [ $( $val1:expr => $val2:expr ),* ] => {{
    let v = vec![ $( NameElse::Else( ( $val1, $val2 ) ) ),* ];
    let l = list_of_vec( &v );
    let pval = obj::PVal::Dict( l );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }};
}

#[macro_export]
macro_rules! othunk {
  [ $body:expr ] => {{
    let pval = obj::PVal::OpenThunk( $body );
    obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
  }}
}

#[macro_export]
macro_rules! olam {
  { $var:ident . $body:expr } => {{
    let pexp = obj::PExp::Lam(stringify!($var).to_string(), $body);
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
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
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
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
    obj::Exp{pexp:Box::new(pe), cann:refl::CTyp::Unk}
  }};
}

#[macro_export]
macro_rules! olet {
  { $var:ident = $rhs:expr ; $body:expr } => {{
    let pexp = obj::PExp::Let(stringify!($var).to_string(), $rhs, $body);
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }};
  { $var1:ident = $rhs1:expr , $( $var2:ident = $rhs2:expr ),+ ; $body:expr } => {{
    olet!($var1 = $rhs1 ; olet!( $( $var2 = $rhs2 ),+ ; $body ))
  }};
}

#[macro_export]
macro_rules! oproj {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Proj( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! ohalt {
  ( ) => {{
    let pexp = obj::PExp::Prim(obj::Prim::Halt);
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}


// #[macro_export]
// macro_rules! oprim {
//   ( $prim:expr ) => {{
//     let pexp = obj::PExp::Prim( $prim );
//     let exp  = obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk};
//     let pval = obj::PVal::Thunk( adapton::collections::map_empty(), exp );
//     obj::Val{pval:Box::new(pval), vann:refl::VTyp::Unk}
//   }}
// }

#[macro_export]
macro_rules! oopendb {
  ( $v1:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbOpen( $v1 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! ofilterdb {
  ( $v1:expr, $v2:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbFilter( $v1, $v2 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! oeq {
  ( $v1:expr, $v2:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::Eq( $v1, $v2 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! ojoindb {
  ( $v1:expr, $v2:expr, $v3:expr, $v4:expr ) => {{
    let pexp = obj::PExp::Prim( obj::Prim::DbJoin($v1, $v2, $v3, $v4 ) );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! ovarf {
  ( $var:ident ) => {{
    let v = ovar!($var);
    obj::Exp{pexp:Box::new(obj::PExp::Force(v)),
             cann:refl::CTyp::Unk}
  }};
}

#[macro_export]
macro_rules! oref {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ref( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! oget {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Get( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! oset {
  ( $val1:expr , $val2:expr ) => {{
    let pexp = obj::PExp::Set( $val1, $val2 );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

#[macro_export]
macro_rules! oret {
  ( $val:expr ) => {{
    let pexp = obj::PExp::Ret( $val );
    obj::Exp{pexp:Box::new(pexp), cann:refl::CTyp::Unk}
  }}
}

