use std::{fmt, rc::Rc};

#[derive(Debug)]
pub enum Data {
  List(Vec<Rc<Data>>),
  Symbol(String),
  String(String),
  Boolean(bool),
  Integer(i64),
  Float(f64),
}

impl fmt::Display for Data {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Data::*;

    match self {
      List(xs) => {
        let mut first = true;
        write!(f, "(")?;
        for x in xs {
          if first { first = false; } else { write!(f, " ")?; }
          x.fmt(f)?;
        }
        write!(f, ")")
      },
      Symbol(name) => {
        write!(f, "{}", &name)
      },
      String(s) => write!(f, "\"{}\"", s),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Integer(x) => write!(f, "{}", x),
      Float(x) => write!(f, "{}", x),
    }
  }
}

