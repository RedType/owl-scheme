use std::{
  fmt,
  rc::Rc,
};
use bimap::BiMap;

#[derive(Debug, Default)]
pub struct IdTable {
  table: BiMap<String, usize>, 
  next_id: usize,
}

impl IdTable {
  pub fn new() -> Self {
    Self {
      table: BiMap::new(),
      next_id: 0,
    }
  }

  pub fn get(&mut self, name: &str) -> usize {
    if let Some(id) = self.table.get_by_left(name) {
      *id
    } else {
      let id = self.next_id;
      self.next_id += 1;
      self.table.insert(name.to_owned(), id);

      id
    }
  }

  pub fn lookup(&self, id: usize) -> Option<&str> {
    self.table.get_by_right(&id).map(|x| x.as_str())
  }
}

#[derive(Debug)]
pub enum Data {
  List(Vec<Rc<Data>>),
  Symbol(usize),
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
      Symbol(_) => {
        todo!();
      },
      String(x) => write!(f, "\"{}\"", x),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Integer(x) => write!(f, "{}", x),
      Float(x) => write!(f, "{}", x),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn table_insert() {
    let mut table = IdTable::new();

    let asdf = table.get("asdf");
    assert_eq!(table.get("asdf"), asdf);

    let fdsa = table.get("fdsa");
    assert_eq!(table.get("fdsa"), fdsa);

    assert_ne!(asdf, fdsa);
  }

  #[test]
  fn table_lookup() {
    let mut table = IdTable::new();

    assert_eq!(table.lookup(0), None);
    assert_eq!(table.lookup(678), None);

    let asdf = table.get("asdf");
    let fdsa = table.get("fdsa");

    assert_eq!(table.lookup(asdf), Some("asdf"));
    assert_eq!(table.lookup(fdsa), Some("fdsa"));
  }
}

