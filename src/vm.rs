use crate::{
  data::{BuiltinFn, Data, Env, GcData, SymbolTable},
  error::EvalError,
  stdlib,
  util::LRU,
};
use gc::{Gc, GcCell};
use log::*;
use prime_factorization::Factorization;
use std::{
  cell::{RefCell, UnsafeCell},
  collections::HashMap,
  fmt::Write,
  hash::{DefaultHasher, Hash, Hasher},
  ptr,
  rc::Rc,
};

#[derive(Debug)]
pub struct VM {
  builtins: HashMap<Rc<str>, Rc<dyn BuiltinFn>>,
  pub symbols: SymbolTable,
  factors_memo: UnsafeCell<HashMap<u64, Vec<u64>>>,
  factors_eviction_queue: RefCell<LRU<u64>>,
}

impl VM {
  const MEMO_SZ: usize = 10_000;

  pub fn new() -> Self {
    Self {
      builtins: HashMap::new(),
      symbols: SymbolTable::new(),
      factors_memo: UnsafeCell::new(HashMap::with_capacity(Self::MEMO_SZ)),
      factors_eviction_queue: RefCell::new(LRU::with_capacity(Self::MEMO_SZ)),
    }
  }

  pub fn def_builtin<F: BuiltinFn + 'static, S: AsRef<str>>(&mut self, name: S, code: F) {
    let sym = self.symbols.add(name);
    if let Data::Symbol(ref name) = sym {
      let replaced = self.builtins.insert(Rc::clone(name), Rc::new(code));
      if replaced.is_some() {
        error!("Redefined {}, a builtin function. You probably don't want to do this.", name);
      }
    } else {
      unreachable!();
    }
  }

  pub fn fetch_builtin<S: AsRef<str>>(&self, name: S) -> Option<Data> {
    let named_code = self.builtins.get_key_value(name.as_ref());
    named_code.map(|(name, code)| Data::Builtin(Rc::clone(name), Rc::clone(code)))
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
      unsafe { (*factors_memo).remove(&evict); }
    }

    let Factorization { factors, .. } = Factorization::run(n);

    unsafe { let _ = (*factors_memo).insert(n, factors); }
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
          write!(f, "{}{:+}i", *r, *i)
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
      Procedure(name, args, proc) => {
        let mut hasher = DefaultHasher::new();
        for arg in args {
          arg.hash(&mut hasher);
        }
        ptr::hash(proc, &mut hasher);
        let hash = hasher.finish() % 16u64.pow(6);
        if let Some(name) = name {
          write!(f, "<procedure {} {:x}>", name, hash)
        } else {
          write!(f, "<procedure {:x}>", hash)
        }
      },
    }.unwrap();
  }

  pub fn eval(&self, env: &Rc<Env>, expr: GcData) -> Result<GcData, EvalError> {
    use Data::*;

    match *expr.borrow() {
      // self-evaluating expressions
      Boolean(_)
      | String(_)
      | Complex(_, _)
      | Real(_)
      | Rational(_, _)
      | Integer(_)
      | Builtin(_, _)
      | Procedure(_, _, _) => Ok(Gc::clone(&expr)),

      // variable lookup
      Symbol(ref name) => env.lookup(name).ok_or(EvalError::UnboundSymbol),

      // function application & special forms
      List(ref exps) => match exps.front().as_ref() {
        None => Err(EvalError::NonFunctionApplication),
        Some(gcdata) => match *gcdata.borrow() {
          ///////////////////
          // special forms //
          ///////////////////

          Symbol(ref s) if *s == "lambda".into() => {
            // get lambda name, if applicable
            let name = if exps.len() == 3 {
              // this is an anonymous lambda (without a name)
              None
            } else if exps.len() == 4 {
              // this lambda is named
              if let Symbol(ref name) = *exps[1].borrow() {
                Some(Rc::clone(name))
              } else {
                return Err(EvalError::InvalidLambdaName);
              }
            } else {
              return Err(EvalError::InvalidSpecialForm);
            };

            // construct parameter list
            let mut parameters = Vec::new();
            if let List(ref ps) = *exps[1].borrow() {
              parameters.reserve_exact(ps.len());
              for p in ps {
                if let Symbol(ref s) = *p.borrow() {
                  parameters.push(Rc::clone(s));
                } else {
                  return Err(EvalError::InvalidParameter);
                }
              }
            } else {
              return Err(EvalError::InvalidParameterList);
            }

            // build procedure
            let proc = Procedure(name, parameters, Gc::clone(&exps[2]));

            Ok(Gc::new(GcCell::new(proc)))
          },

          Symbol(ref s) if *s == "quote".into() => {
            if exps.len() != 2 {
              Err(EvalError::InvalidSpecialForm)
            } else {
              Ok(Gc::clone(&exps[1]))
            }
          },

          Symbol(ref s) if *s == "let".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "let*".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "letrec".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "define".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "set!".into() => {
            if exps.len() != 2 {
              Err(EvalError::InvalidSpecialForm)
            } else {
              let res = env.set(s, &exps[1]);
              Ok(Gc::new(GcCell::new(Boolean(res))))
            }
          },

          Symbol(ref s) if *s == "if".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "cond".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "case".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "and".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "or".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "begin".into() => {
            todo!();
          },

          Symbol(ref s) if *s == "do".into() => {
            todo!();
          },

          // procedure call
          Procedure(ref _name, _, _) => {
            todo!();
          },

          _ => Err(EvalError::NonFunctionApplication),
        },
      },
    }
  }

  pub fn apply(&self, f: Data, args: Data) -> Data {
    Data::nil()
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
  use gc::{Gc, GcCell};
  use std::collections::VecDeque;
  use crate::{
    data::Data,
    vm::VM,
  };

  #[test]
  fn display_data() {
    use Data::*;

    let mut vm = VM::new();

    let symbol = vm.symbols.add("jeremy");
    assert_eq!(vm.display_data(&symbol), "jeremy".to_owned());

    let string = String("upright bass".to_owned());
    assert_eq!(vm.display_data(&string), "\"upright bass\"");

    let tru = Boolean(true);
    let fals = Boolean(false);
    assert_eq!(vm.display_data(&tru), "#true");
    assert_eq!(vm.display_data(&fals), "#false");

    let int = Integer(35);
    assert_eq!(vm.display_data(&int), "35");

    let float = Real(123.4);
    assert_eq!(vm.display_data(&float), "123.4");

    let nil = Data::nil();
    assert_eq!(vm.display_data(&nil), "()");

    let list = List(
      [symbol, string, tru, fals, int, float, nil]
        .into_iter()
        .map(GcCell::new)
        .map(Gc::new)
        .collect::<VecDeque<_>>()
    );
    assert_eq!(vm.display_data(&list), "(jeremy \"upright bass\" #true #false 35 123.4)");

    let dotted = List(
      [Real(12.0), String("oy".into()), Data::nil(), Real(0.23456)]
        .into_iter()
        .map(GcCell::new)
        .map(Gc::new)
        .collect::<VecDeque<_>>()
    );
    assert_eq!(vm.display_data(&dotted), "(12 \"oy\" () . 0.23456)");
  }

  #[test]
  fn display_numbers() {
    use Data::*;

    let mut vm = VM::new();

    let complex = Complex(123.4, 5.0);
    assert_eq!(vm.display_data(&complex), "123.4+5i");

    let complex2 = Complex(123.4, -5.0);
    assert_eq!(vm.display_data(&complex2), "123.4-5i");

    let complex3 = Complex(0.0, -5.0);
    assert_eq!(vm.display_data(&complex3), "-5i");

    let complex4 = Complex(1.1, 0.0);
    assert_eq!(vm.display_data(&complex4), "1.1");

    let rational = Rational(-3, 4);
    assert_eq!(vm.display_data(&rational), "-3/4");

    let rational2 = Rational(0, 4);
    assert_eq!(vm.display_data(&rational2), "0");

    let rational3 = Rational(4, 1);
    assert_eq!(vm.display_data(&rational3), "4");
  }

  #[test]
  fn factorize() {
    let vm = VM::new();

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
    let mut vm = VM::new();

    let g5 = vm.gcf(5, 15);
    assert_eq!(g5, 5);

    let g1 = vm.gcf(7757 * 7, 27);
    assert_eq!(g1, 1);

    let g4 = vm.gcf(4 * 7, 4 * 13);
    assert_eq!(g4, 4);
  }
}

