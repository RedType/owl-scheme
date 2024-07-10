use crate::{
  data::{BuiltinFn, Data, DataCell, Env, SymbolTable},
  error::{EvalError, SourceInfo, VMError},
  stdlib,
  util::{Or, LRU},
};
use gc::Gc;
use prime_factorization::Factorization;
use std::{
  cell::{RefCell, UnsafeCell},
  collections::HashMap,
  fmt::Write,
  fs::File,
  io::Read,
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

  pub fn eval_str<S: AsRef<str>>(
    &mut self,
    source: S,
  ) -> Result<Gc<DataCell>, VMError> {
    let source = source.as_ref().chars();
    let lexemes = self.lex(source)?;
    let asts = self.build_ast(lexemes)?;
    asts
      .into_iter()
      .map(|ast| self.eval(&Rc::clone(&self.global_env), ast, false))
      .reduce(|a, data| a.and(data))
      .unwrap()
  }

  pub fn eval(
    &mut self,
    env: &Rc<Env>,
    expr: Gc<DataCell>,
    allow_placeholders: bool,
  ) -> Result<Gc<DataCell>, VMError> {
    use Data::*;

    match expr.data {
      Nil { .. } => {
        Err(VMError::new(EvalError::NilEvaluation, expr.info.clone()))
      },
      // self-evaluating expressions
      Boolean(_)
      | String(_)
      | Complex(_, _)
      | Real(_)
      | Rational(_, _)
      | Integer(_)
      | Builtin { .. }
      | Procedure { .. } => Ok(Gc::clone(&expr)),

      Placeholder => {
        if allow_placeholders {
          Ok(Gc::clone(&expr))
        } else {
          Err(VMError::new(
            EvalError::IllegalPlaceholder,
            expr.info.clone(),
          ))
        }
      },

      // variable lookup
      Symbol(ref name) => env.lookup(name).ok_or(VMError::new(
        EvalError::UnboundSymbol(Rc::clone(name)),
        expr.info.clone(),
      )),

      // function application & special forms
      List { list: ref exps, .. } => match exps.borrow().front().as_ref() {
        None => Err(VMError::new(EvalError::NilEvaluation, expr.info.clone())),
        Some(head) => match head.data {
          ///////////////////
          // special forms //
          ///////////////////
          Symbol(ref s) if *s == "lambda".into() => {
            let exps = exps.borrow();
            build_proc(exps.iter().skip(1), exps.len() - 1, head.info.clone())
          },

          Symbol(ref s) if *s == "quote".into() => {
            let exps = exps.borrow();
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
            let exps = exps.borrow();
            // binding syntax
            if exps.len() == 3 {
              let Symbol(ref fn_name) = exps[1].data else {
                return Err(VMError::new(
                  EvalError::InvalidSpecialForm,
                  head.info.clone(),
                ));
              };
              env.bind(fn_name, self.eval(env, Gc::clone(&exps[2]), false)?);
              Ok(DataCell::new_info(
                Data::Nil { print: false },
                head.info.clone(),
              ))

            // function declaration syntax
            } else if exps.len() == 4 {
              let Symbol(ref fn_name) = exps[1].data else {
                return Err(VMError::new(
                  EvalError::InvalidSpecialForm,
                  head.info.clone(),
                ));
              };
              let proc =
                build_proc(exps.iter().skip(1), exps.len() - 1, head.info.clone())?;
              env.bind(fn_name, proc);
              Ok(DataCell::new_info(
                Data::Nil { print: false },
                head.info.clone(),
              ))

            // invalid define
            } else {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            }
          },

          Symbol(ref s) if *s == "set!".into() => {
            let exps = exps.borrow();
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
            let exps = exps.borrow();
            if exps.len() != 4 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              // evaluate condition
              match self.eval(env, Gc::clone(&exps[1]), false)?.data {
                Boolean(true) => self.eval(env, Gc::clone(&exps[2]), false),
                Boolean(false) => self.eval(env, Gc::clone(&exps[3]), false),
                _ => Err(VMError::new(
                  EvalError::NonBooleanTest,
                  head.info.clone(),
                )),
              }
            }
          },

          Symbol(ref s) if *s == "include".into() => {
            let exps = exps.borrow();
            if exps.len() != 2 {
              Err(VMError::new(
                EvalError::InvalidSpecialForm,
                head.info.clone(),
              ))
            } else {
              if let String(ref s) = exps[1].data {
                // read file
                let mut source = std::string::String::new();
                match File::open(&*s.borrow()) {
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
                  evaluated = self.eval(env, code, false)?;
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
            let exps = exps.borrow();
            let headval = self.eval(env, Gc::clone(*head), false)?;
            let res = match headval.data {
              // procedure call
              Procedure {
                ref name,
                ref parameters,
                varargs,
                ref arguments,
                ref code,
              } => {
                let given_args_len = exps.len() - 1;
                // short circuit if no arguments given to a non-zero-arg function
                if parameters.len() != 0 && given_args_len == 0 {
                  return Ok(headval);
                }
                self.apply(
                  &env,
                  name.as_ref(),
                  head.info.clone(),
                  Or::A(parameters),
                  varargs,
                  arguments,
                  exps.iter().skip(1).cloned(),
                  Or::A(code),
                )
              },

              // builtin call
              Builtin {
                ref name,
                parameters,
                varargs,
                ref arguments,
                ref code,
              } => {
                let given_args_len = exps.len() - 1;
                // short circuit if no arguments given to a non-zero-arg function
                if parameters != 0 && given_args_len == 0 {
                  return Ok(headval);
                }
                self.apply(
                  env,
                  Some(&name),
                  head.info.clone(),
                  Or::B(parameters),
                  varargs,
                  arguments,
                  exps.iter().skip(1).cloned(),
                  Or::B(code),
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
    name: Option<&Rc<str>>,
    info: SourceInfo,
    parameters: Or<&[Rc<str>], usize>,
    mut varargs: bool,
    preapplied_arguments: &[Option<Gc<DataCell>>],
    given_arguments: I,
    code: Or<&Gc<DataCell>, &Rc<dyn BuiltinFn>>,
  ) -> Result<Gc<DataCell>, VMError> {
    use Data::*;

    let param_ct = parameters.fuse(|a| a.len(), |b| *b);

    // evaluate given arguments
    let mut eval_arguments = given_arguments
      .into_iter()
      .map(|a| self.eval(env, Gc::clone(&a), true))
      .peekable();

    // prepare full arguments
    let mut full_arguments: Vec<Option<Gc<DataCell>>> =
      Vec::with_capacity(param_ct);
    let mut preapplied_arguments = preapplied_arguments.iter().cloned();
    let mut unbound_params = 0;

    // build full_arguments array
    for _ in 0..param_ct {
      match preapplied_arguments.next() {
        // argument was present
        Some(Some(arg)) => full_arguments.push(Some(arg)),
        // placeholder or no arg was present
        Some(None) | None => match eval_arguments.next() {
          // argument was given
          Some(arg) => {
            let arg = arg?;
            match arg.data {
              // argument given was a placeholder
              Placeholder => {
                unbound_params += 1;
                full_arguments.push(None);
              },
              // argument given was a value
              _ => full_arguments.push(Some(arg)),
            }
          },
          // no argument was given
          None => {
            unbound_params += 1;
            full_arguments.push(None);
          },
        },
      }
    }

    // build varargs
    if varargs {
      if let Some(true) = full_arguments.last().map(|a| a.is_some()) {
        let last = full_arguments.pop().flatten().unwrap();
        let mut full_varargs = vec![last];

        // consume arguments given past end
        for arg in eval_arguments {
          full_varargs.push(arg?);
        }
        full_arguments.push(Some(DataCell::new_info(
          Data::list(full_varargs),
          info.clone(),
        )));

        varargs = false;
      } else if eval_arguments.peek().is_some() {
        // a placeholder was given for final named parameter, but more arguments
        // were given afterwards
        return Err(VMError::new(EvalError::PlaceholderInVarargs, info));
      }
    // check for extraneous arguments
    } else if eval_arguments.peek().is_some() {
      return Err(VMError::new(EvalError::TooManyArguments, info));
    }

    // check for partial application
    if unbound_params > 0 || param_ct > full_arguments.len() {
      let new_proc_name = name.as_ref().map(|name| {
        let mut new_proc_name = name.to_string();
        write!(new_proc_name, "_p{}", unbound_params).unwrap();
        Rc::from(new_proc_name)
      });

      let new_partial =
        match parameters {
          Or::A(parameters) => Procedure {
            name: new_proc_name,
            parameters: parameters.iter().cloned().collect::<_>(),
            varargs,
            arguments: full_arguments,
            code: Gc::clone(&code.expect_a(
              "Tried to apply a non-builtin param list to a builtin",
            )),
          },
          Or::B(parameters) => Builtin {
            name: new_proc_name.expect("All builtins must be named"),
            parameters,
            varargs,
            arguments: full_arguments,
            code: Rc::clone(&code.expect_b(
              "Tried to apply a builtin param list to a non-builtin",
            )),
          },
        };

      Ok(DataCell::new_info(new_partial, info))

    // full application
    } else {
      let new_env = Rc::new(env.new_scope());

      // unwrap arguments
      let mut unwrapped_arguments = Vec::new();
      for arg in full_arguments {
        unwrapped_arguments.push(arg.unwrap());
      }

      match parameters {
        // normal procedure
        Or::A(parameters) => {
          // bind arguments
          let binds = parameters.iter().zip(unwrapped_arguments);
          for (p, a) in binds {
            new_env.bind(p, a);
          }

          // evaluate and return
          self.eval(
            &new_env,
            Gc::clone(&code.expect_a(
              "Tried to apply a non-builtin param list to a builtin",
            )),
            false,
          )
        },
        // builtin procedure
        Or::B(_) => {
          let code = code
            .expect_b("Tried to apply a builtin param list to a non-builtin");

          // unlistify varargs
          if unwrapped_arguments.last().map(|l| l.has_list()).unwrap_or(false) {
            let last = unwrapped_arguments.pop().unwrap();
            let Data::List { ref list, .. } = last.data else {
              unreachable!();
            };
            for arg in list.borrow().iter().cloned() {
              unwrapped_arguments.push(arg);
            }
          }

          code(self, &unwrapped_arguments)
            .map(|data| DataCell::new_info(data, info.clone()))
            .map_err(|err| VMError(err, info.clone()))
        },
      }
    }
  }
}

/////////////
// Helpers //
/////////////
fn build_proc<'a, I>(
  mut exps: I,
  len: usize,
  info: SourceInfo,
) -> Result<Gc<DataCell>, VMError>
where
  I: Iterator<Item = &'a Gc<DataCell>>,
{
  use Data::*;

  // get proc name, if applicable
  let name = if len == 2 {
    // this is an anonymous lambda (without a name)
    None
  } else if len == 3 {
    // this lambda is named
    if let Symbol(ref name) = exps.next().unwrap().data {
      Some(Rc::clone(name))
    } else {
      return Err(VMError::new(EvalError::InvalidLambdaName, info));
    }
  } else {
    return Err(VMError::new(EvalError::InvalidSpecialForm, info));
  };

  // construct parameter list
  let mut parameters = Vec::new();
  let varargs;
  match exps.next().unwrap().data {
    List { ref list, dotted } => {
      varargs = dotted;
      parameters.reserve_exact(list.borrow().len());
      for parameter in list.borrow().iter() {
        match parameter.data {
          Symbol(ref name) => parameters.push(Rc::clone(name)),
          Placeholder => {
            return Err(VMError::new(
              EvalError::PlaceholderInParameterList,
              info,
            ))
          },
          _ => return Err(VMError::new(EvalError::InvalidParameter, info)),
        }
      }
    },
    _ => {
      return Err(VMError::new(EvalError::NonSymbolInParameterList, info));
    },
  }

  // build procedure
  let proc = Procedure {
    name,
    parameters,
    varargs,
    arguments: Vec::new(),
    code: Gc::clone(exps.next().unwrap()),
  };

  Ok(DataCell::new_info(proc, info))
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
