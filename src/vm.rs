use std::{
  collections::{HashMap, HashSet, VecDeque},
  fmt,
  rc::Rc,
};
use gc::{Finalize, GcCell, Trace};
use log::*;
use crate::{
  data::{BuiltinFn, Data, SymbolTable},
  std,
  util::Sieve,
}

#[derive(Debug)]
pub struct VM {
  builtins: HashMap<Rc<str>, Rc<BuiltinFn>>,
  symbols: SymbolTable,
  prime_sieve: Sieve,
  factors_memo: HashMap<u64, Vec<u64>>,
}

impl VM {
  pub fn new() -> Self {
    Self {
      builtins: HashMap::new(),
      symbols: SymbolTable::new(),
      prime_sieve: Sieve::new(),
      factors_memo: HashMap::new(),
    }
  }

  pub fn def_builtin<F: BuiltinFn, S: AsRef<str>>(&mut self, name: S, code: F) {
    let sym = self.symbols.add(name);
    let replaced = self.builtins.insert(Rc::clone(sym.0), Rc::new(code));
    if replaced.is_some() {
      warn!("Redefined a builtin function. You probably don't want to do this.");
    }
  }

  pub fn fetch_builtin<S: AsRef<str>>(&self, name: S) -> Option<Data> {
    let named_code = self.builtins.get_key_value(name);
    named_code.map(|(name, code)| Data::Builtin(Rc::clone(name), Rc::clone(code)))
  }

  pub fn factorize(&mut self, n: u64) -> &[u64] {
    if let Some(factors) = self.factors_memo.get(n) {
      return factors;
    }

    let mut a = n;
    let mut factors = Vec::new();

    for p in self.prime_sieve.sieve(n) {
      if a == 0 || a == 1 { break; }

      while a % p == 0 {
        a /= p;
        factors += p;
      }
    }

    self.factors_memo.insert(n, factors);
    self.factors_memo.get(n).unwrap()
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

  pub fn rat(&mut self, numerator: i64, denominator: i64) -> Data {
    let sign_correction = if denominator < 0 { -1 } else { 1 };
    let gcf = self.gcf(numerator.abs() as u64, denominator.abs() as u64);
    Data::Rational(sign_correction * numerator / gcf, denominator / gcf)
  }
}

impl Default for VM {
  fn default() -> Self {
    let mut me = VM::new();
    std::import_std(&mut me);
    me
  }
}

