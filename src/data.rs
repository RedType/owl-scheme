use crate::{
  error::{ArithmeticError, SourceInfo},
  vm::VM,
};
use gc::{Finalize, Gc, GcCell, Trace};
use std::{
  cell::RefCell,
  collections::{HashMap, HashSet, VecDeque},
  error::Error,
  fmt,
  hash::{DefaultHasher, Hash, Hasher},
  ptr,
  rc::Rc,
};

// trait alias
pub trait BuiltinFn:
  Fn(&mut VM, &[Gc<DataCell>]) -> Result<Data, Box<dyn Error>>
{
}
impl<T: Fn(&mut VM, &[Gc<DataCell>]) -> Result<Data, Box<dyn Error>>> BuiltinFn
  for T
{
}

impl fmt::Debug for dyn BuiltinFn {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "<builtin fn>")
  }
}

#[derive(Clone, Debug, Finalize, Trace)]
pub struct DataCell {
  pub data: Data,
  pub info: SourceInfo,
}

impl DataCell {
  pub fn new(data: Data) -> Gc<Self> {
    Self::new_info(data, SourceInfo::blank())
  }

  pub fn new_info(data: Data, info: SourceInfo) -> Gc<Self> {
    Gc::new(Self { data, info })
  }
}

#[derive(Clone, Debug, Finalize, Trace)]
pub enum Data {
  Nil {
    print: bool,
  },
  List {
    list: GcCell<VecDeque<Gc<DataCell>>>,
    dotted: bool,
  },
  Placeholder,
  Symbol(Rc<str>),
  String(GcCell<String>),
  Boolean(bool),
  Builtin {
    name: Rc<str>,
    parameters: usize,
    varargs: bool,
    arguments: Vec<Option<Gc<DataCell>>>, // for partial application
    #[unsafe_ignore_trace]
    code: Rc<dyn BuiltinFn>,
  },
  Procedure {
    name: Option<Rc<str>>,
    parameters: Vec<Rc<str>>,
    varargs: bool,
    arguments: Vec<Option<Gc<DataCell>>>, // for partial application
    code: Gc<DataCell>,
  },
  // numbers
  Complex(f64, f64),
  Real(f64),
  Rational(i64, i64),
  Integer(i64),
}

impl Data {
  pub fn nil() -> Self {
    Self::Nil { print: true }
  }

  pub fn list<I: IntoIterator<Item = Gc<DataCell>>>(items: I) -> Self {
    Self::List {
      list: GcCell::new(items.into_iter().collect::<VecDeque<_>>()),
      dotted: false,
    }
  }

  pub fn dotted_list<I: IntoIterator<Item = Gc<DataCell>>>(items: I) -> Self {
    Self::List {
      list: GcCell::new(items.into_iter().collect::<VecDeque<_>>()),
      dotted: true,
    }
  }

  pub fn is_nil(&self) -> bool {
    if let Self::Nil { .. } = self {
      true
    } else if let Self::List { list, .. } = self {
      list.borrow().is_empty()
    } else {
      false
    }
  }

  pub fn clone_numeric(&self) -> Result<Data, ArithmeticError> {
    match *self {
      Self::Integer(i) => Ok(Self::Integer(i)),
      Self::Real(r) => Ok(Self::Real(r)),
      Self::Rational(n, d) => Ok(Self::Rational(n, d)),
      Self::Complex(r, i) => Ok(Self::Complex(r, i)),
      _ => Err(ArithmeticError::NonNumericArgument(self.clone())),
    }
  }
}

impl PartialEq for Data {
  fn eq(&self, other: &Self) -> bool {
    use Data::*;

    match (self, other) {
      (Nil { .. }, Nil { .. }) => true,
      (Nil { .. }, data) | (data, Nil { .. }) => data.is_nil(),
      (List { list: l, .. }, List { list: r, .. }) => {
        if l.borrow().len() != r.borrow().len() {
          false
        } else {
          l.borrow()
            .iter()
            .zip(r.borrow().iter())
            .map(|(l, r)| l.data == r.data)
            .fold(true, |a, x| a && x)
        }
      },
      (Symbol(l), Symbol(r)) => Rc::ptr_eq(l, r),
      (String(l), String(r)) => l == r,
      (Boolean(l), Boolean(r)) => l == r,
      (Builtin { code: l, .. }, Builtin { code: r, .. }) => Rc::ptr_eq(l, r),
      (Procedure { code: l, .. }, Procedure { code: r, .. }) => {
        Gc::ptr_eq(l, r)
      },
      (Rational(ln, ld), Rational(rn, rd)) => {
        ln * *rd as i64 == rn * *ld as i64
      },
      (Integer(l), Integer(r)) => l == r,
      (Complex(lr, li), Complex(rr, ri)) => {
        (lr - rr).abs() < 0.0000001 && (li - ri).abs() < 0.0000001
      },
      (Real(l), Real(r)) => (l - r).abs() < 0.0000001,
      (Placeholder, Placeholder) => true,
      _ => false,
    }
  }
}

impl fmt::Display for Data {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    use Data::*;

    match self {
      Nil { print: true } => write!(f, "()"),
      Nil { print: false } => Ok(()),

      List { list, dotted } => {
        let borrow = list.borrow();
        let mut iter = borrow.iter().peekable();
        let mut first = true;

        write!(f, "(");
        while let Some(x) = iter.next() {
          let last = iter.peek().is_none();
          // write leading space
          if first {
            first = false;
          } else {
            write!(f, " ");
          }

          let _ = &x.data.fmt(f);
          // check to see if we're at the end
          // if so, print a dot if dotted
          // otherwise just print the element
          if !last {
            x.data.fmt(f);
          } else if *dotted {
            write!(f, " . ");
            x.data.fmt(f);
          }
        }
        write!(f, ")")
      },
      Symbol(name) => write!(f, "{}", name),
      String(x) => write!(f, "\"{}\"", x.borrow()),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Complex(r, i) => {
        if *i == 0.0 {
          write!(f, "{}", r)
        } else if *r == 0.0 {
          write!(f, "{}i", i)
        } else {
          write!(f, "{}{:+}i", r, i)
        }
      },
      Real(x) => write!(f, "{}", x),
      Rational(n, d) => {
        if *d == 1 {
          write!(f, "{}", n)
        } else if *n == 0 {
          write!(f, "0")
        } else {
          write!(f, "{}/{}", n, d)
        }
      },
      Integer(x) => write!(f, "{}", x),
      Builtin { name, .. } => write!(f, "<builtin fn {}>", name),
      Procedure {
        name,
        parameters,
        varargs: _,
        arguments,
        code,
      } => {
        let mut hasher = DefaultHasher::new();
        for param in parameters {
          param.hash(&mut hasher);
        }
        for arg in arguments {
          ptr::hash(arg, &mut hasher);
        }
        ptr::hash(code, &mut hasher);
        let hash = hasher.finish() % 16u64.pow(6);
        if let Some(name) = name {
          write!(f, "<procedure {} {:x}>", name, hash)
        } else {
          write!(f, "<procedure {:x}>", hash)
        }
      },
      Placeholder => write!(f, "_"),
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
    self
      .0
      .get(name.as_ref())
      .map(|item| Data::Symbol(Rc::clone(item)))
  }
}

#[derive(Debug)]
pub struct Env {
  bindings: RefCell<HashMap<Rc<str>, Gc<DataCell>>>,
  prev_scope: Option<Rc<Env>>,
}

impl Env {
  pub fn new() -> Self {
    Self {
      bindings: RefCell::new(HashMap::new()),
      prev_scope: None,
    }
  }

  pub fn new_scope(self: &Rc<Self>) -> Self {
    Env {
      bindings: RefCell::new(HashMap::new()),
      prev_scope: Some(Rc::clone(self)),
    }
  }

  pub fn bind(&self, name: &Rc<str>, value: Gc<DataCell>) {
    let _ = self.bindings.borrow_mut().insert(Rc::clone(name), value);
  }

  pub fn set(&self, name: &Rc<str>, value: &Gc<DataCell>) -> bool {
    if let Some(old_value) = self.bindings.borrow_mut().get_mut(name) {
      *old_value = Gc::clone(value);
      true
    } else if let Some(ref prev_scope) = self.prev_scope {
      prev_scope.set(name, value)
    } else {
      false
    }
  }

  pub fn lookup(&self, name: &Rc<str>) -> Option<Gc<DataCell>> {
    self
      .bindings
      .borrow()
      .get(name)
      .map(|data| Gc::clone(data))
      .or(self.prev_scope.as_ref().and_then(|prev| prev.lookup(name)))
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
    };
  }

  #[test]
  fn table_add() {
    let mut table = SymbolTable::new();

    let asdf_sym = table.add("asdf");
    let fdsa_sym = table.add("fdsa?");
    let asdf2_sym = table.add("asdf");
    let asdf = unsym!(asdf_sym);
    let fdsa = unsym!(fdsa_sym);
    let asdf2 = unsym!(asdf2_sym);

    assert_ne!(asdf_sym, fdsa_sym);
    assert_eq!(asdf_sym, asdf2_sym);

    assert_eq!(asdf, &Rc::from("asdf"));
    assert_eq!(fdsa, &Rc::from("fdsa?"));
    assert_eq!(asdf2, &Rc::from("asdf"));
  }

  #[test]
  fn table_get() {
    let mut table = SymbolTable::new();

    assert!(table.get("asdf").is_none());

    let asdf = table.add("asdf");

    assert_eq!(table.get("asdf").unwrap(), asdf);
  }

  #[test]
  fn display_data() {
    use Data::*;

    let mut vm = VM::no_std();

    let symbol = vm.symbols.add("jeremy");
    assert_eq!(symbol.to_string(), "jeremy".to_owned());

    let string = String(GcCell::new("upright bass".to_owned()));
    assert_eq!(string.to_string(), "\"upright bass\"");

    let tru = Boolean(true);
    let fals = Boolean(false);
    assert_eq!(tru.to_string(), "#true");
    assert_eq!(fals.to_string(), "#false");

    let int = Integer(35);
    assert_eq!(int.to_string(), "35");

    let float = Real(123.4);
    assert_eq!(float.to_string(), "123.4");

    let nil = Data::nil();
    assert_eq!(nil.to_string(), "()");

    let list = Data::list(
      [symbol, string, tru, fals, int, float]
        .into_iter()
        .map(|e| DataCell::new_info(e, SourceInfo::blank()))
        .collect::<VecDeque<_>>(),
    );
    assert_eq!(
      list.to_string(),
      "(jeremy \"upright bass\" #true #false 35 123.4)"
    );

    let dotted = Data::dotted_list(
      [
        Real(12.0),
        String(GcCell::new("oy".into())),
        Data::nil(),
        Real(0.23456),
      ]
      .into_iter()
      .map(|e| DataCell::new_info(e, SourceInfo::blank()))
      .collect::<VecDeque<_>>()
    );
    assert_eq!(dotted.to_string(), "(12 \"oy\" () . 0.23456)");
  }

  #[test]
  fn display_numbers() {
    use Data::*;

    let complex = Complex(123.4, 5.0);
    assert_eq!(complex.to_string(), "123.4+5i");

    let complex2 = Complex(123.4, -5.0);
    assert_eq!(complex2.to_string(), "123.4-5i");

    let complex3 = Complex(0.0, -5.0);
    assert_eq!(complex3.to_string(), "-5i");

    let complex4 = Complex(1.1, 0.0);
    assert_eq!(complex4.to_string(), "1.1");

    let rational = Rational(-3, 4);
    assert_eq!(rational.to_string(), "-3/4");

    let rational2 = Rational(0, 4);
    assert_eq!(rational2.to_string(), "0");

    let rational3 = Rational(4, 1);
    assert_eq!(rational3.to_string(), "4");
  }

  macro_rules! gcdata {
    ($e:expr) => {
      Gc::new(DataCell::new_info($e, SourceInfo::blank()))
    };
  }

  #[test]
  fn env() {
    let env = Env::new();

    let hello_sym = Rc::from("hello");
    let hello_data = gcdata!(Data::String(GcCell::new("Hello".into())));
    env.bind(&hello_sym, Gc::clone(&hello_data));

    let hello_lookup = env.lookup(&hello_sym).unwrap();
    match (&hello_lookup.data, &hello_data.data) {
      (&Data::String(ref l), &Data::String(ref r)) => {
        assert_eq!(*l.borrow(), *r.borrow());
      },
      _ => panic!(),
    }
  }

  #[test]
  fn env_nested() {
    let env = Rc::new(Env::new());

    let hello_sym = Rc::from("hello");
    let hello_data = gcdata!(Data::String(GcCell::new("Hello".into())));
    env.bind(&hello_sym, Gc::clone(&hello_data));

    let nested_env = env.new_scope();

    let goodbye_data = gcdata!(Data::String(GcCell::new("Goodbye".into())));
    nested_env.bind(&hello_sym, Gc::clone(&goodbye_data));

    let global_lookup = env.lookup(&hello_sym).unwrap();
    match (&global_lookup.data, &hello_data.data) {
      (&Data::String(ref l), &Data::String(ref r)) => {
        assert_eq!(*l.borrow(), *r.borrow());
      },
      _ => panic!(),
    }

    let nested_lookup = nested_env.lookup(&hello_sym).unwrap();
    match (&nested_lookup.data, &goodbye_data.data) {
      (&Data::String(ref l), &Data::String(ref r)) => {
        assert_eq!(*l.borrow(), *r.borrow());
      },
      _ => panic!(),
    }
  }
}
