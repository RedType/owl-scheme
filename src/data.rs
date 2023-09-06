use std::{
  collections::HashMap,
  fmt,
  rc::Rc,
};

#[derive(Debug)]
pub enum Data {
  List(Vec<Rc<Data>>),
  Symbol(usize, Rc<str>),
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
      (Symbol(x, _), Symbol(y, _)) => x == y,
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
      Symbol(_, name) => write!(f, "{}", name),
      String(x) => write!(f, "\"{}\"", x),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Integer(x) => write!(f, "{}", x),
      Float(x) => write!(f, "{}", x),
    }
  }
}

#[derive(Debug, Default)]
pub struct IdTable {
  table: HashMap<Rc<str>, usize>,
  lookup: Vec<Rc<str>>, 
  next_id: usize,
}

impl IdTable {
  pub fn new() -> Self {
    Self {
      table: HashMap::new(),
      lookup: Vec::new(),
      next_id: 0,
    }
  }

  pub fn add(&mut self, name: &str) -> Data {
    if let Some(&id) = self.table.get(name) {
      Data::Symbol(id, Rc::clone(&self.lookup[id]))
    } else {
      let id = self.next_id;
      self.next_id += 1;
      let own_name: Rc<str> = Rc::from(name);
      self.table.insert(Rc::clone(&own_name), id);
      self.lookup.push(Rc::clone(&own_name));

      Data::Symbol(id, own_name)
    }
  }

  pub fn get(&self, name: &str) -> Option<usize> {
    self.table.get(name).copied()
  }

  pub fn get_sym(&self, name: &str) -> Option<Data> {
    self.table.get(name).map(|&id| Data::Symbol(id, Rc::clone(&self.lookup[id])))
  }

  pub fn lookup(&self, id: usize) -> Option<Rc<str>> {
    self.lookup.get(id).map(Rc::clone)
  }

  pub fn lookup_sym(&self, id: usize) -> Option<Data> {
    self.lookup.get(id).map(|name| Data::Symbol(id, Rc::clone(name)))
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  macro_rules! unsym {
    ($sym:expr) => {
      if let Data::Symbol(id, ref name) = $sym {
        (id, name)
      } else {
        panic!("{:?} must be a Data::Symbol", $sym);
      }
    }
  }


  #[test]
  fn table_add() {
    let mut table = IdTable::new();

    let asdf_sym = table.add("asdf");
    let fdsa_sym = table.add("fdsa");
    let asdf_sym_2 = table.add("asdf");
    let asdf = unsym!(asdf_sym);
    let fdsa = unsym!(fdsa_sym);
    let asdf2 = unsym!(asdf_sym_2);

    assert_ne!(asdf, fdsa);
    assert_eq!(asdf, asdf2);

    assert_ne!(asdf.0, fdsa.0);
    assert_eq!(asdf.0, asdf2.0);

    assert_eq!(asdf.1, &Rc::from("asdf"));
    assert_eq!(fdsa.1, &Rc::from("fdsa"));
    assert_eq!(asdf2.1, &Rc::from("asdf"));
  }

  #[test]
  fn table_get() {
    let mut table = IdTable::new();

    assert_eq!(table.get("asdf"), None);
    assert_eq!(table.get("fdsa"), None);

    let (asdf, _) = unsym!(table.add("asdf"));
    let (fdsa, _) = unsym!(table.add("fdsa"));

    assert_eq!(table.get("asdf"), Some(asdf));
    assert_eq!(table.get("fdsa"), Some(fdsa));
    assert_ne!(table.get("asdf"), table.get("fdsa"));
  }

  #[test]
  fn table_get_sym() {
    let mut table = IdTable::new();

    assert_eq!(table.get_sym("asdf"), None);

    let asdf = table.add("asdf");

    assert_eq!(table.get_sym("asdf").unwrap(), asdf);
  }

  #[test]
  fn table_lookup() {
    let mut table = IdTable::new();

    assert_eq!(table.lookup(678), None);
    assert_eq!(table.lookup(0), None);
    assert_eq!(table.lookup(usize::MAX), None);

    let asdf_sym = table.add("asdf");
    let fdsa_sym = table.add("fdsa");
    let asdf = unsym!(asdf_sym).0;
    let fdsa = unsym!(fdsa_sym).0;

    assert_eq!(table.lookup(asdf), Some(Rc::from("asdf")));
    assert_eq!(table.lookup(fdsa), Some(Rc::from("fdsa")));

    assert_eq!(table.lookup(asdf.saturating_add(fdsa).saturating_add(1)), None);
  }

  #[test]
  fn table_lookup_sym() {
    let mut table = IdTable::new();

    assert_eq!(table.lookup_sym(1234), None);
    assert_eq!(table.lookup_sym(0), None);
    assert_eq!(table.lookup_sym(usize::MAX), None);

    let asdf = table.add("asdf");
    let (id, _) = unsym!(asdf);

    assert_eq!(table.lookup_sym(id), Some(asdf));

    assert_eq!(table.lookup_sym(id.saturating_add(1)), None);
  }
}

