use std::{
  collections::{HashSet, VecDeque},
  fmt,
  rc::Rc,
};
use gc::{Finalize, GcCell, Trace};

// trait alias
pub trait BuiltinFn: FnMut(&mut Data) -> Result<Data, ()> {}
impl<T: FnMut(&mut Data) -> Result<Data, ()>> BuiltinFn for T {}

impl fmt::Debug for dyn BuiltinFn {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "<builtin fn>")
  }
}

#[derive(Debug, Finalize, Trace)]
pub enum Data {
  List(VecDeque<GcCell<Data>>),
  Symbol(Rc<str>),
  String(String),
  Boolean(bool),
  // first element is the fn name
  Builtin(Rc<str>, #[unsafe_ignore_trace] Rc<dyn BuiltinFn>),
  // numbers
  Complex(f64, f64),
  Real(f64),
  Rational(i64, u64),
  Integer(i64),
}

impl Data {
  pub fn nil() -> Data {
    Self::List(VecDeque::new())
  }

  pub fn is_nil(&self) -> bool {
    if let Self::List(xs) = self {
      xs.is_empty()
    } else {
      false
    }
  }
}

impl PartialEq for Data {
  fn eq(&self, other: &Self) -> bool {
    use Data::*;
    match (self, other) {
      (List(l), List(r)) => {
        if l.len() != r.len() {
          false
        } else {
          l.iter().zip(r.iter())
            .map(|(l, r)| *l.borrow() == *r.borrow())
            .fold(true, |a, x| a && x)
        }
      },
      (Symbol(l), Symbol(r)) => Rc::ptr_eq(l, r),
      (String(l), String(r)) => l == r,
      (Boolean(l), Boolean(r)) => l == r,
      (Builtin(_, l), Builtin(_, r)) => Rc::ptr_eq(l, r),
      (Complex(lr, li), Complex(rr, ri)) => lr == rr && li == ri,
      (Real(l), Real(r)) => l == r,
      (Rational(_, _), Rational(_, _)) => unimplemented!("Rationals are unreduced"),
      (Integer(l), Integer(r)) => l == r,
      _ => false,
    }
  }
}
impl Eq for Data {}

#[derive(Debug, Default)]
pub struct SymbolTable(HashSet<Rc<str>>);

impl SymbolTable {
  pub fn new() -> Self {
    Self(HashSet::new())
  }

  pub fn add<S: AsRef<str>>(&mut self, name: S) -> Data {
    if let Some(item) = self.0.get(name.as_ref()) {
      Data::Symbol(Rc::clone(item))
    } else {
      let item = Rc::from(name.as_ref());
      self.0.insert(Rc::clone(&item));
      Data::Symbol(item)
    }
  }

  pub fn get<S: AsRef<str>>(&self, name: S) -> Option<Data> {
    self.0.get(name.as_ref()).map(|item| Data::Symbol(Rc::clone(item)))
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! unsym {
    ($sym:expr) => {
      if let Data::Symbol(ref name) = $sym {
        name
      } else {
        panic!("{:?} must be a Data::Symbol", $sym);
      }
    }
  }

  #[test]
  fn table_add() {
    let mut table = SymbolTable::new();

    let asdf_sym = table.add("asdf");
    let fdsa_sym = table.add("fdsa");
    let asdf2_sym = table.add("asdf");
    let asdf = unsym!(asdf_sym);
    let fdsa = unsym!(fdsa_sym);
    let asdf2 = unsym!(asdf2_sym);

    assert_ne!(asdf_sym, fdsa_sym);
    assert_eq!(asdf_sym, asdf2_sym);

    assert_eq!(asdf, &Rc::from("asdf"));
    assert_eq!(fdsa, &Rc::from("fdsa"));
    assert_eq!(asdf2, &Rc::from("asdf"));
  }

  #[test]
  fn table_get() {
    let mut table = SymbolTable::new();

    assert_eq!(table.get("asdf"), None);

    let asdf = table.add("asdf");

    assert_eq!(table.get("asdf").unwrap(), asdf);
  }
}

