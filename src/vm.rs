use crate::{
  data::{BuiltinFn, Data, DataCell, Env, SymbolTable},
  error::{EvalError, SourceInfo, VMError},
  stdlib,
  util::LRU,
};
use gc::Gc;
use prime_factorization::Factorization;
use std::{
  cell::{RefCell, UnsafeCell},
  collections::HashMap,
  fmt::Write,
  fs::File,
  hash::{DefaultHasher, Hash, Hasher},
  io::Read,
  ptr,
  rc::Rc,
};

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
          if first {
            first = false;
          } else if !last {
            write!(f, " ").unwrap();
          }

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
      Builtin { name, .. } => write!(f, "<builtin fn {}>", name),
      Procedure {
        name,
        parameters,
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
    }
    .unwrap();
  }

  pub fn eval_str<S: AsRef<str>>(
    &mut self,
    source: S,
  ) -> Result<Gc<DataCell>, VMError> {
    let source = source.as_ref().chars();
    let lexemes = self.lex(source)?;
    let asts = self.build_ast(lexemes).unwrap();
    asts
      .into_iter()
      .map(|ast| self.eval(&Rc::clone(&self.global_env), ast))
      .reduce(|a, data| a.and(data))
      .unwrap()
  }

  pub fn eval(
    &mut self,
    env: &Rc<Env>,
    expr: Gc<DataCell>,
  ) -> Result<Gc<DataCell>, VMError> {
    use Data::*;

    match *expr.borrow() {
      // self-evaluating expressions
      Boolean(_)
      | String(_)
      | Complex(_, _)
      | Real(_)
      | Rational(_, _)
      | Integer(_)
      | Builtin { .. }
      | Procedure { .. } => Ok(Gc::clone(&expr)),

      // variable lookup
      Symbol(ref name) => env.lookup(name).ok_or(VMError::new(
        EvalError::UnboundSymbol(Rc::clone(name)),
        expr.info.clone(),
      )),

      // function application & special forms
      List(ref exps) => match exps.front().as_ref() {
        None => Err(VMError::new(
          EvalError::EmptyListEvaluation,
          expr.info.clone(),
        )),
        Some(head) => match *head.borrow() {
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
                return Err(VMError::new(
                  EvalError::InvalidLambdaName,
                  head.info.clone(),
                ));
              }
            } else {
              return Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ));
            };

            // construct parameter list
            let mut parameters = Vec::new();
            if let List(ref ps) = *exps[1].borrow() {
              parameters.reserve_exact(ps.len());
              for p in ps {
                if let Symbol(ref s) = *p.borrow() {
                  parameters.push(Rc::clone(s));
                } else {
                  return Err(VMError::new(
                    EvalError::InvalidParameter,
                    head.info.clone(),
                  ));
                }
              }
            } else {
              return Err(VMError::new(
                EvalError::InvalidParameterList,
                head.info.clone(),
              ));
            }

            // build procedure
            let proc = Procedure {
              name,
              parameters,
              arguments: Vec::new(),
              code: Gc::clone(&exps[2]),
            };

            Ok(DataCell::new_info(proc, head.info.clone()))
          },

          Symbol(ref s) if *s == "quote".into() => {
            if exps.len() != 2 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              Ok(Gc::clone(&exps[1]))
            }
          },

          Symbol(ref s) if *s == "define".into() => {
            if exps.len() != 3 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else if let Symbol(ref s) = &*exps[1].borrow() {
              env.bind(s, self.eval(env, Gc::clone(&exps[2]))?);
              Ok(DataCell::new_info(Data::nil(), head.info.clone()))
            } else {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            }
          },

          Symbol(ref s) if *s == "set!".into() => {
            if exps.len() != 2 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              if env.set(s, &exps[1]) {
                Ok(DataCell::new_info(Data::nil(), head.info.clone()))
              } else {
                Err(VMError::new(
                  EvalError::UnboundSymbol(Rc::clone(s)),
                  head.info.clone(),
                ))
              }
            }
          },

          Symbol(ref s) if *s == "if".into() => {
            if exps.len() != 4 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              // evaluate condition
              match &*self.eval(env, Gc::clone(&exps[1]))?.borrow() {
                Boolean(true) => self.eval(env, Gc::clone(&exps[2])),
                Boolean(false) => self.eval(env, Gc::clone(&exps[3])),
                _ => Err(VMError::new(
                  EvalError::NonBooleanTest,
                  head.info.clone(),
                )),
              }
            }
          },

          Symbol(ref s) if *s == "include".into() => {
            if exps.len() != 2 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              if let String(s) = &*exps[1].borrow() {
                // read file
                let mut source = std::string::String::new();
                match File::open(s) {
                  Ok(mut f) => match f.read_to_string(&mut source) {
                    Ok(_) => Ok(()),
                    Err(e) => Err(VMError::new(
                      EvalError::IOError(e),
                      head.info.clone(),
                    )),
                  },
                  Err(e) => {
                    Err(VMError::new(EvalError::IOError(e), head.info.clone()))
                  },
                }?;

                // lex and parse file
                let lexemes = self.lex(source.chars())?;
                let codes = self.build_ast(lexemes)?;

                let mut evaluated =
                  DataCell::new_info(Data::nil(), head.info.clone());
                for code in codes {
                  evaluated = self.eval(env, code)?;
                }

                Ok(evaluated)
              } else {
                Err(VMError::new(
                  EvalError::InvalidSpecialForm,
                  head.info.clone(),
                ))
              }
            }
          },

          // function application
          _ => {
            let headval = self.eval(env, Gc::clone(*head))?;
            let res = match *headval.borrow() {
              // procedure call
              Procedure {
                ref name,
                ref parameters,
                ref arguments,
                ref code,
              } => {
                let given_args_len = exps.len() - 1;
                self.apply(
                  &env,
                  name,
                  head.info.clone(),
                  parameters,
                  arguments,
                  exps.iter().skip(1).cloned(),
                  given_args_len,
                  code,
                )
              },

              // builtin call
              Builtin {
                ref name,
                parameters,
                ref arguments,
                ref code,
              } => {
                let given_args_len = exps.len() - 1;

                self.apply_builtin(
                  name,
                  head.info.clone(),
                  parameters,
                  arguments,
                  exps.iter().skip(1).cloned(),
                  given_args_len,
                  code,
                )
              },

              ref e => Err(VMError::new(
                EvalError::NonFunctionApplication(e.clone()),
                head.info.clone(),
              )),
            };
            res
          },
        },
      },
    }
  }

  pub fn apply<I: IntoIterator<Item = Gc<DataCell>>>(
    &mut self,
    env: &Rc<Env>,
    name: &Option<Rc<str>>,
    info: SourceInfo,
    parameters: &[Rc<str>],
    preapplied_arguments: &[Gc<DataCell>],
    given_arguments: I,
    given_arguments_count: usize,
    code: &Gc<DataCell>,
  ) -> Result<Gc<DataCell>, VMError> {
    use Data::*;

    // check for partial application
    let remaining =
      parameters.len() - preapplied_arguments.len() - given_arguments_count;

    if remaining > 0 {
      // this is a partial application
      let new_proc_name = name.as_ref().map(|name| {
        let mut new_proc_name = name.to_string();
        write!(new_proc_name, "_p{}", remaining).unwrap();
        Rc::from(new_proc_name)
      });

      let full_arguments = preapplied_arguments
        .iter()
        .cloned()
        .chain(given_arguments.into_iter())
        .collect::<_>();

      let new_partial = Procedure {
        name: new_proc_name,
        parameters: parameters.iter().cloned().collect::<_>(),
        arguments: full_arguments,
        code: Gc::clone(&code),
      };

      Ok(DataCell::new_info(new_partial, info))
    } else if remaining == 0 {
      // this is a full application
      let new_env = Rc::new(env.new_scope());

      // apply arguments
      let full_arguments = preapplied_arguments
        .iter()
        .cloned()
        .chain(given_arguments.into_iter());
      let binds = parameters.iter().zip(full_arguments);
      for (p, a) in binds {
        new_env.bind(p, a);
      }

      // evaluate and return
      self.eval(&new_env, Gc::clone(&code))
    } else {
      // too many arguments applied
      Err(VMError::new(EvalError::TooManyArguments, info))
    }
  }

  pub fn apply_builtin<I: IntoIterator<Item = Gc<DataCell>>>(
    &mut self,
    name: &Rc<str>,
    info: SourceInfo,
    parameters: usize,
    preapplied_arguments: &[Gc<DataCell>],
    given_arguments: I,
    given_arguments_count: usize,
    code: &Rc<dyn BuiltinFn>,
  ) -> Result<Gc<DataCell>, VMError> {
    use Data::*;

    // check for partial application
    let remaining =
      parameters - preapplied_arguments.len() - given_arguments_count;

    if remaining > 0 {
      // this is a partial application
      let mut new_proc_name_buffer = name.to_string();
      write!(new_proc_name_buffer, "_p{}", remaining).unwrap();
      let new_proc_name = Rc::from(new_proc_name_buffer);

      let full_arguments = preapplied_arguments
        .iter()
        .cloned()
        .chain(given_arguments.into_iter())
        .collect::<_>();

      let new_partial = Builtin {
        name: new_proc_name,
        parameters: remaining,
        arguments: full_arguments,
        code: Rc::clone(&code),
      };

      Ok(DataCell::new_info(new_partial, info))
    } else if remaining == 0 {
      // this is a full application
      let full_arguments = preapplied_arguments
        .iter()
        .cloned()
        .chain(given_arguments.into_iter())
        .collect::<Vec<_>>();

      // evaluate and return
      code(&full_arguments)
        .map(|data| DataCell::new_info(data, info.clone()))
        .map_err(|err| VMError(err, info.clone()))
    } else {
      // too many arguments applied
      Err(VMError(Box::new(EvalError::TooManyArguments), info))
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::{
    data::{Data, DataCell},
    error::SourceInfo,
    vm::VM,
  };
  use std::collections::VecDeque;

  #[test]
  fn display_data() {
    use Data::*;

    let mut vm = VM::no_std();

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
        .map(|e| DataCell::new_info(e, SourceInfo::blank()))
        .collect::<VecDeque<_>>(),
    );
    assert_eq!(
      vm.display_data(&list),
      "(jeremy \"upright bass\" #true #false 35 123.4)"
    );

    let dotted = List(
      [Real(12.0), String("oy".into()), Data::nil(), Real(0.23456)]
        .into_iter()
        .map(|e| DataCell::new_info(e, SourceInfo::blank()))
        .collect::<VecDeque<_>>(),
    );
    assert_eq!(vm.display_data(&dotted), "(12 \"oy\" () . 0.23456)");
  }

  #[test]
  fn display_numbers() {
    use Data::*;

    let mut vm = VM::no_std();

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
