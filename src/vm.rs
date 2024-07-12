use crate::{
  data::{BuiltinFn, Data, DataCell, Env, SymbolTable},
  error::SourceInfo,
  stdlib,
  util::LRU,
};
use prime_factorization::Factorization;
use std::{
  cell::{RefCell, UnsafeCell},
  collections::HashMap,
  rc::Rc,
};

pub mod eval;

#[derive(Debug)]
pub struct VM {
  pub global_env: Rc<Env>,
  pub symbols: SymbolTable,
  factors_memo: UnsafeCell<HashMap<u64, Vec<u64>>>,
  factors_eviction_queue: RefCell<LRU<u64>>,
}

impl VM {
  const MEMO_SZ: usize = 10_000;

  pub fn no_std() -> Self {
    Self {
      global_env: Rc::new(Env::new()),
      symbols: SymbolTable::new(),
      factors_memo: UnsafeCell::new(HashMap::with_capacity(Self::MEMO_SZ)),
      factors_eviction_queue: RefCell::new(LRU::with_capacity(Self::MEMO_SZ)),
    }
  }

  pub fn new() -> Self {
    let mut me = Self::no_std();
    stdlib::import_std(&mut me);
    me
  }

  pub fn def_builtin<F: BuiltinFn + 'static, S: AsRef<str>>(
    &mut self,
    name: S,
    parameters: usize,
    varargs: bool,
    code: F,
  ) {
    // create/retrieve symbol
    let sym = self.symbols.add(name);
    let Data::Symbol(ref name) = sym else {
      unreachable!();
    };

    // register builtin
    self.global_env.bind(
      name,
      DataCell::new_info(
        Data::Builtin {
          name: Rc::clone(name),
          parameters,
          varargs,
          arguments: Vec::new(),
          code: Rc::new(code),
        },
        SourceInfo::blank(),
      ),
    );
  }

  // SAFETY: the factors_memo pointer is only used in this function, so
  // it should be safe to use like this right???
  pub fn factorize(&self, n: u64) -> &[u64] {
    let factors_memo = self.factors_memo.get();
    if unsafe { (*factors_memo).contains_key(&n) } {
      // update LRU
      self.factors_eviction_queue.borrow_mut().touch(&n);
      return unsafe { (*factors_memo).get(&n).unwrap() };
    }

    // check for eviction
    let len = unsafe { (*factors_memo).len() };
    debug_assert!(len <= Self::MEMO_SZ);
    debug_assert!(len == self.factors_eviction_queue.borrow().len());
    if len >= Self::MEMO_SZ {
      let evict = self.factors_eviction_queue.borrow_mut().dequeue().unwrap();
      unsafe {
        (*factors_memo).remove(&evict);
      }
    }

    let Factorization { factors, .. } = Factorization::run(n);

    unsafe {
      let _ = (*factors_memo).insert(n, factors);
    }
    self.factors_eviction_queue.borrow_mut().enqueue(n);
    unsafe { &(*factors_memo).get(&n).unwrap() }
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

  pub fn rational(&mut self, n: i64, d: i64) -> Data {
    let gcf = self.gcf(n.abs() as u64, d.abs() as u64) as i64;

    if n >= 0 && d >= 0 {
      Data::Rational(n / gcf, d / gcf)
    } else if n >= 0 && d < 0 {
      Data::Rational(-n / gcf, -d / gcf)
    } else if n < 0 && d >= 0 {
      Data::Rational(n / gcf, d / gcf)
    } else if n < 0 && d < 0 {
      Data::Rational(-n / gcf, -d / gcf)
    } else {
      unreachable!();
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::vm::VM;

  #[test]
  fn factorize() {
    let vm = VM::no_std();

    let f200 = vm.factorize(200);
    assert_eq!(f200, &[2, 2, 2, 5, 5]);

    let f5_7_11 = vm.factorize(5 * 7 * 11);
    assert_eq!(f5_7_11, &[5, 7, 11]);

    let f2 = vm.factorize(2);
    assert_eq!(f2, &[2]);

    let f7757_13 = vm.factorize(7757 * 13);
    assert_eq!(f7757_13, &[13, 7757]);
  }

  #[test]
  fn gcf() {
    let mut vm = VM::no_std();

    let g5 = vm.gcf(5, 15);
    assert_eq!(g5, 5);

    let g1 = vm.gcf(7757 * 7, 27);
    assert_eq!(g1, 1);

    let g4 = vm.gcf(4 * 7, 4 * 13);
    assert_eq!(g4, 4);
  }
}
