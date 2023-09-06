use std::{
  collections::HashSet,
  fmt,
  rc::Rc,
};

#[derive(Debug)]
pub enum Data {
  List(Vec<Rc<Data>>),
  Symbol(Rc<str>),
  String(String),
  Boolean(bool),
  Integer(i64),
  Float(f64),
}

impl PartialEq for Data {
  fn eq(&self, other: &Data) -> bool {
    use Data::*;

    match (self, other) {
      (List(xs), List(ys)) => xs == ys,
      (Symbol(x), Symbol(y)) => Rc::ptr_eq(x, y),
      (String(x), String(y)) => x == y,
      (Boolean(x), Boolean(y)) => x == y,
      (Integer(x), Integer(y)) => x == y,
      (Float(x), Float(y)) => x == y, // you should know better
      _ => false,
    }
  }
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
      Symbol(name) => write!(f, "{}", name),
      String(x) => write!(f, "\"{}\"", x),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Integer(x) => write!(f, "{}", x),
      Float(x) => write!(f, "{}", x),
    }
  }
}

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

  #[test]
  fn display() {
    use Data::*;

    let mut table = SymbolTable::new();
    let symbol = table.add("jeremy");
    assert_eq!(symbol.to_string(), "jeremy");

    let string = String("upright bass".to_owned());
    assert_eq!(string.to_string(), "\"upright bass\"");

    let tru = Boolean(true);
    let fals = Boolean(false);
    assert_eq!(tru.to_string(), "#true");
    assert_eq!(fals.to_string(), "#false");

    let int = Integer(35);
    assert_eq!(int.to_string(), "35");

    let float = Float(123.4);
    assert_eq!(float.to_string(), "123.4");

    let list = List(
      [symbol, string, tru, fals, int, float]
        .into_iter()
        .map(Rc::new)
        .collect::<Vec<_>>()
    );
    assert_eq!(list.to_string(), "(jeremy \"upright bass\" #true #false 35 123.4)");
  }

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

