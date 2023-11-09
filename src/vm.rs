use crate::{
  data::{BuiltinFn, Data, SymbolTable},
  stdlib,
  util::LRU,
};
use log::*;
use prime_factorization::Factorization;
use std::{
  collections::HashMap,
  fmt::Write,
  rc::Rc,
};

#[derive(Debug)]
pub struct VM {
  builtins: HashMap<Rc<str>, Rc<dyn BuiltinFn>>,
  pub symbols: SymbolTable,
  factors_memo: HashMap<u64, Vec<u64>>,
  factors_eviction_queue: LRU<u64>,
}

impl VM {
  const MEMO_SZ: usize = 10_000;

  pub fn new() -> Self {
    Self {
      builtins: HashMap::new(),
      symbols: SymbolTable::new(),
      factors_memo: HashMap::with_capacity(Self::MEMO_SZ),
      factors_eviction_queue: LRU::with_capacity(Self::MEMO_SZ),
    }
  }

  pub fn def_builtin<F: BuiltinFn, S: AsRef<str>>(&mut self, name: S, code: F) {
    let sym = self.symbols.add(name);
    if let Data::Symbol(name) = sym {
      let replaced = self.builtins.insert(Rc::clone(&name), Rc::new(code));
      if replaced.is_some() {
        warn!("Redefined {}, a builtin function. You probably don't want to do this.", name);
      }
    } else {
      unreachable!();
    }
  }

  pub fn fetch_builtin<S: AsRef<str>>(&self, name: S) -> Option<Data> {
    let named_code = self.builtins.get_key_value(name.as_ref());
    named_code.map(|(name, code)| Data::Builtin(Rc::clone(name), Rc::clone(code)))
  }

  pub fn factorize(&mut self, n: u64) -> &[u64] {
    if let Some(factors) = self.factors_memo.get(&n) {
      // update LRU
      self.factors_eviction_queue.touch(n);
      return factors;
    }

    // check for eviction
    debug_assert!(self.factors_memo.len() <= Self::MEMO_SZ);
    debug_assert!(self.factors_memo.len() == self.factors_eviction_queue.len());
    if self.factors_memo.len() >= Self::MEMO_SZ {
      let evict = self.factors_eviction_queue.dequeue().unwrap();
      self.factors_memo.remove(&evict);
    }

    let Factorization { factors, .. } = Factorization::run(n);

    self.factors_memo.insert(n, factors);
    self.factors_eviction_queue.enqueue(n);
    &self.factors_memo.get(&n).unwrap()[..]
  }

  pub fn gcf(&mut self, m: u64, n: u64) -> u64 {
    let factors_m = self.factorize(m);
    let factors_n = self.factorize(n);
    let mut common_factors = Vec::new();

    let mut i_m = 0;
    let mut i_n = 0;

    while i_m < factors_m.len() && i_n < factors_n.len() {
      if factors_m[i_m] == factors_n[i_n] {
        common_factors.push(factors_m[i_m]);
        i_m += 1;
        i_n += 1;
      } else if factors_m[i_m] < factors_n[i_n] {
        i_m += 1;
      } else {
        i_n += 1;
      }
    }

    common_factors.iter().fold(1, |a, f| a * f)
  }

  pub fn display_data(&mut self, d: &Data) -> String {
    let mut output = String::new();
    self.display_data_rec(&mut output, d);
    output
  }

  fn display_data_rec(&mut self, f: &mut String, d: &Data) {
    use Data::*;

    match d {
      List(xs) => {
        let mut iter = xs.iter().peekable();
        let mut first = true;

        write!(f, "(").unwrap();
        while let Some(x) = iter.next() {
          let last = iter.peek().is_none();
          // write leading space
          if first { first = false; } else if !last { write!(f, " ").unwrap(); }

          // check to see if we're at the end
          // if so, print a dot for non-nil and print nothing for nil
          // otherwise just print the element
          if !last {
            self.display_data_rec(f, &x.borrow());
          } else if !x.borrow().is_nil() {
            write!(f, " . ").unwrap();
            self.display_data_rec(f, &x.borrow());
          }
        }
        write!(f, ")")
      },
      Symbol(name) => write!(f, "{}", name),
      String(x) => write!(f, "\"{}\"", x),
      Boolean(x) => write!(f, "{}", if *x { "#true" } else { "#false" }),
      Complex(r, i) => {
        if *i == 0.0 {
          write!(f, "{}", *r)
        } else if *r == 0.0 {
          write!(f, "{}i", *i)
        } else {
          let sign = if *i < 0.0 { "-" } else { "+" };
          write!(f, "{}{}{}i", *r, sign, *i)
        }
      },
      Real(x) => write!(f, "{}", x),
      Rational(n, d) => {
        // reduce
        let gcf = self.gcf(n.abs() as u64, *d);
        let (rn, rd) = (*n / gcf as i64, *d / gcf);

        if rd == 1 {
          write!(f, "{}", rn)
        } else if rn == 0 {
          write!(f, "0")
        } else {
          write!(f, "{}/{}", rn, rd)
        }
      },
      Integer(x) => write!(f, "{}", x),
      Builtin(name, _) => write!(f, "<builtin fn {}>", name),
    }.unwrap();
  }
}

impl Default for VM {
  fn default() -> Self {
    let mut me = VM::new();
    stdlib::import_std(&mut me);
    me
  }
}

#[cfg(test)]
mod tests {
  use gc::GcCell;
  use std::collections::VecDeque;
  use crate::{
    data::{Data, SymbolTable},
    vm::VM,
  };

  #[test]
  fn display_data() {
    use Data::*;

    let mut vm = VM::new();

    let symbol = vm.symbols.add("jeremy");
    assert_eq!(vm.display_data(symbol), "jeremy".to_owned());

    let string = String("upright bass".to_owned());
    assert_eq!(vm.display_data(string), "\"upright bass\"");

    let tru = Boolean(true);
    let fals = Boolean(false);
    assert_eq!(vm.display_data(tru), "#true");
    assert_eq!(vm.display_data(fals), "#false");

    let int = Integer(35);
    assert_eq!(vm.display_data(int), "35");

    let float = Real(123.4);
    assert_eq!(vm.display_data(float), "123.4");

    let nil = Data::nil();
    assert_eq!(vm.display_data(nil), "()");

    let list = List(
      [symbol, string, tru, fals, int, float, nil]
        .into_iter()
        .map(GcCell::new)
        .collect::<VecDeque<_>>()
    );
    assert_eq!(vm.display_data(list), "(jeremy \"upright bass\" #true #false 35 123.4)");

    let dotted = List(
      [Real(12.0), String("oy".into()), Data::nil(), Real(0.23456)]
        .into_iter()
        .map(GcCell::new)
        .collect::<VecDeque<_>>()
    );
    assert_eq!(vm.display_data(dotted), "(12 \"oy\" () . 0.23456)");
  }

  #[test]
  fn display_numbers() {
    use Data::*;

    let mut vm = VM::new();

    let complex = Complex(123.4, 5.0);
    assert_eq!(vm.display_data(complex), "123.4+5.0i");

    let complex2 = Complex(123.4, -5.0);
    assert_eq!(vm.display_data(complex2), "123.4-5.0i");

    let complex3 = Complex(0.0, -5.0);
    assert_eq!(vm.display_data(complex3), "-5.0i");

    let complex4 = Complex(1.1, 0.0);
    assert_eq!(vm.display_data(complex4), "1.1");

    let rational = Rational(3, -4);
    assert_eq!(vm.display_data(rational), "-3/4");

    let rational2 = Rational(0, 4);
    assert_eq!(vm.display_data(rational2), "0");

    let rational3 = Rational(4, 1);
    assert_eq!(vm.display_data(rational3), "4");
  }
}

