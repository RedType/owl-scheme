use crate::{
  data::{Data, DataCell},
  error::{ArithmeticError, UnspecifiedError},
  vm::VM,
};
use gc::GcCell;
use std::{
  f64::consts,
  io::{self, Write},
};

pub fn import_std(vm: &mut VM) {
  use Data::*;

  // constants
  if let Symbol(ref nan) = vm.symbols.add("NaN") {
    vm.global_env.bind(nan, DataCell::new(Real(f64::NAN)));
  } else {
    unreachable!();
  }

  if let Symbol(ref inf) = vm.symbols.add("Inf") {
    vm.global_env.bind(inf, DataCell::new(Real(f64::INFINITY)));
  } else {
    unreachable!();
  }

  if let Symbol(ref neg_inf) = vm.symbols.add("-Inf") {
    vm.global_env
      .bind(neg_inf, DataCell::new(Real(f64::NEG_INFINITY)));
  } else {
    unreachable!();
  }

  if let Symbol(ref pi) = vm.symbols.add("pi") {
    vm.global_env.bind(pi, DataCell::new(Real(consts::PI)));
  } else {
    unreachable!();
  }

  if let Symbol(ref e) = vm.symbols.add("e") {
    vm.global_env.bind(e, DataCell::new(Real(consts::E)));
  } else {
    unreachable!();
  }

  if let Symbol(ref i) = vm.symbols.add("i") {
    vm.global_env.bind(i, DataCell::new(Complex(0.0, 1.0)));
  } else {
    unreachable!();
  }

  if let Symbol(ref neg_i) = vm.symbols.add("-i") {
    vm.global_env.bind(neg_i, DataCell::new(Complex(0.0, -1.0)));
  } else {
    unreachable!();
  }

  // functions
  vm.def_builtin("OvO", 0, false, |_, _| {
    // auto-format whyyyyy ;A;
    const OWL: &'static str = concat!(
      "() ()  meow!\n",
      "(OvO) /     \n",
      "(| |)       \n",
      " ^ ^        ",
    );
    Ok(String(GcCell::new(OWL.to_string())))
  });

  vm.def_builtin("OwO", 0, false, |_, _| {
    const LUGIA: &'static str = concat!(
      "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢻⣦⣄⠀⠀⡄⠀⠀⠀⠀⠀⠀⠀⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⠀⠀⢤⠄⣸⣿⣿⣷⡔⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢣⡀⠈⠻⢿⣿⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣾⣿⣦⣵⡤⢿⠃⠀⠀⠀⠀⠀⠀⠀⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⣷⣄⢠⣿⣿⡟⠻⠇⣠⡾⠀⠀⠀⢠⡀⠀⠀⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⣌⡛⣟⣿⣿⣧⣬⣛⢩⣴⠆⠀⠀⢸⣇⢠⣤⠀⠀\n",
      "⠀⠀⠀⠀⠀⠀⠀⣩⣾⣿⣿⣿⣿⣿⣿⣷⣴⡛⠀⠀⢀⣾⠘⠁⠀⠀\n",
      "⠀⠀⠀⠀⠀⣠⣾⣿⠟⢻⢿⣿⣿⠋⠉⠉⢿⣿⣷⣔⢿⠇⠀⠀⠀⠀\n",
      "⠀⠀⠀⢀⣼⣿⣿⠏⠀⡀⠀⠈⠁⠀⠀⠀⣠⡹⣿⣿⣷⣄⠀⠀⠀⠀\n",
      "⠀⠀⣠⣿⣿⣿⡟⠀⠀⢿⣄⠀⠀⠀⠀⠴⢿⡷⢹⣿⣿⣿⣷⡄⠀⠀\n",
      "⠀⢰⣿⣿⣿⣿⡇⠀⠀⠀⠉⣿⡎⠉⠛⠛⠻⠿⢈⣿⣿⣿⣿⣿⡄⠀\n",
      "⠀⣿⣿⣿⣿⣿⣷⡀⠀⠀⠀⠁⠀⠀⠀⠀⠀⠀⣸⣿⣿⣿⣿⣿⣷⠀\n",
      "⡀⣿⣿⡟⣿⡏⢻⡿⠀⠀⠀⠀⠀⠀⠀⠀⠀⠰⢿⠃⣿⣿⢿⣿⣿⠚\n",
      "⠀⠿⣿⡇⢻⣿⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⡿⠸⠿⠈⠀\n",
      "⠀⠀⠈⠁⠈⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀",
    );
    Ok(String(GcCell::new(LUGIA.to_string())))
  });

  vm.def_builtin("print", 1, true, |_, args| {
    for arg in args {
      print!("{}", arg.data);
    }
    io::stdout().flush()?;
    Ok(Data::Nil { print: false })
  });

  vm.def_builtin("println", 1, true, |_, args| {
    for arg in args {
      print!("{}", arg.data);
    }
    println!();
    Ok(Data::Nil { print: false })
  });

  ////////////////
  // Predicates //
  ////////////////

  vm.def_builtin("null?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| a && x.data.is_nil());
    Ok(Boolean(res))
  });

  vm.def_builtin("number?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("complex?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("real?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(_, i) => i == 0.0,
        Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("rational?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(r, i) => i == 0.0 && r.round() == r,
        Real(n) => n.round() == n,
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("integer?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(r, i) => i == 0.0 && r.round() == r,
        Real(n) => n.round() == n,
        Rational(_, d) => d == 1,
        Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("exact?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("inexact?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(_, _) | Real(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("exact-integer?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Rational(_, d) => d == 1,
        Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("finite?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(r, i) => r.is_finite() && i.is_finite(),
        Real(n) => n.is_finite(),
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("infinite?", 1, true, |_, args| {
    let res = args.iter().fold(true, |a, x| {
      a && match x.data {
        Complex(r, i) => r.is_infinite() || i.is_infinite(),
        Real(n) => n.is_infinite(),
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  /////////////////
  // Comparisons //
  /////////////////

  vm.def_builtin("=", 2, true, |_, xs| {
    let mut eq = true;
    for slice in xs.windows(2) {
      let [a, b] = slice else {
        unreachable!();
      };
      eq = eq && a.data == b.data;
    }
    Ok(Boolean(eq))
  });

  ////////////////
  // Arithmetic //
  ////////////////

  vm.def_builtin("+", 2, true, |vm, xs| {
    xs.iter().fold(Ok(Integer(0)), |a, x| match (a, &x.data) {
      (Ok(Integer(l)), &Integer(r)) => Ok(Integer(l + r)),
      (Ok(Integer(i)), &Rational(n, d)) | (Ok(Rational(n, d)), &Integer(i)) => {
        Ok(vm.rational(i * d + n, d))
      },
      (Ok(Integer(i)), &Real(r)) | (Ok(Real(r)), &Integer(i)) => {
        Ok(Real(r + i as f64))
      },
      (Ok(Integer(n)), &Complex(r, i)) | (Ok(Complex(r, i)), &Integer(n)) => {
        Ok(Complex(r + n as f64, i))
      },
      (Ok(Rational(ln, ld)), &Rational(rn, rd)) => {
        let n = ln * rd + rn * ld;
        let d = ld * rd;
        Ok(vm.rational(n, d))
      },
      (Ok(Rational(n, d)), &Real(r)) | (Ok(Real(r)), &Rational(n, d)) => {
        Ok(Real((n as f64 / d as f64) + r))
      },
      (Ok(Rational(n, d)), &Complex(r, i))
      | (Ok(Complex(r, i)), &Rational(n, d)) => {
        Ok(Complex(n as f64 / d as f64 + r, i))
      },
      (Ok(Real(l)), &Real(r)) => Ok(Real(l + r)),
      (Ok(Real(n)), &Complex(r, i)) | (Ok(Complex(r, i)), &Real(n)) => {
        Ok(Complex(n + r, i))
      },
      (Ok(Complex(lr, li)), &Complex(rr, ri)) => Ok(Complex(lr + rr, li + ri)),

      (Err(l), _) => Err(l),
      (Ok(_), r) => {
        Err(Box::new(ArithmeticError::NonNumericArgument(r.clone())))
      },
    })
  });

  vm.def_builtin("*", 2, true, |vm, xs| {
    xs.iter().fold(Ok(Integer(1)), |a, x| match (a, &x.data) {
      (Ok(Integer(l)), &Integer(r)) => Ok(Integer(l * r)),
      (Ok(Integer(i)), &Rational(n, d)) | (Ok(Rational(n, d)), &Integer(i)) => {
        Ok(vm.rational(i * n, d))
      },
      (Ok(Integer(i)), &Real(r)) | (Ok(Real(r)), &Integer(i)) => {
        Ok(Real(r * i as f64))
      },
      (Ok(Integer(n)), &Complex(r, i)) | (Ok(Complex(r, i)), &Integer(n)) => {
        Ok(Complex(r * n as f64, i * n as f64))
      },
      (Ok(Rational(ln, ld)), &Rational(rn, rd)) => {
        Ok(vm.rational(ln * rn, ld * rd))
      },
      (Ok(Rational(n, d)), &Real(r)) | (Ok(Real(r)), &Rational(n, d)) => {
        Ok(Real((n as f64 / d as f64) * r))
      },
      (Ok(Rational(n, d)), &Complex(r, i))
      | (Ok(Complex(r, i)), &Rational(n, d)) => {
        let rat = n as f64 / d as f64;
        Ok(Complex(rat * r, rat * i))
      },
      (Ok(Real(l)), &Real(r)) => Ok(Real(l * r)),
      (Ok(Real(n)), &Complex(r, i)) | (Ok(Complex(r, i)), &Real(n)) => {
        Ok(Complex(n * r, n * i))
      },
      (Ok(Complex(lr, li)), &Complex(rr, ri)) => {
        Ok(Complex(lr * rr - li * ri, lr * ri + li * rr))
      },

      (Err(l), _) => Err(l),
      (Ok(_), r) => {
        Err(Box::new(ArithmeticError::NonNumericArgument(r.clone())))
      },
    })
  });

  vm.def_builtin("-", 2, true, |vm, xs| {
    if xs.len() == 0 {
      Err(Box::new(UnspecifiedError))
    } else if xs.len() == 1 {
      return match xs[0].data {
        Integer(x) => Ok(Integer(-x)),
        Real(x) => Ok(Real(-x)),
        Rational(n, d) => Ok(vm.rational(-n, d)),
        Complex(r, i) => Ok(Complex(-r, -i)),
        ref x => Err(Box::new(ArithmeticError::NonNumericArgument(x.clone()))),
      };
    } else {
      let mut xs_iter = xs.iter();
      let minuend = xs_iter.next().unwrap().data.clone_numeric()?;
      xs_iter.fold(Ok(minuend), |a, x| match (a, &x.data) {
        (Ok(Integer(l)), &Integer(r)) => Ok(Integer(l - r)),
        (Ok(Integer(l)), &Real(r)) => Ok(Real(l as f64 - r)),
        (Ok(Integer(l)), &Rational(n, d)) => Ok(vm.rational(l * d - n, d)),
        (Ok(Integer(l)), &Complex(r, i)) => Ok(Complex(l as f64 - r, -i)),
        (Ok(Real(l)), &Integer(r)) => Ok(Real(l - r as f64)),
        (Ok(Real(l)), &Real(r)) => Ok(Real(l - r)),
        (Ok(Real(l)), &Rational(n, d)) => Ok(Real(l - n as f64 / d as f64)),
        (Ok(Real(l)), &Complex(r, i)) => Ok(Complex(l - r, i)),
        (Ok(Rational(n, d)), &Integer(r)) => Ok(vm.rational(n - r * d, d)),
        (Ok(Rational(n, d)), &Real(r)) => Ok(Real(n as f64 / d as f64 - r)),
        (Ok(Rational(ln, ld)), &Rational(rn, rd)) => {
          Ok(vm.rational(ln * rd - rn * ld, ld * rd))
        },
        (Ok(Rational(n, d)), &Complex(r, i)) => {
          Ok(Complex(n as f64 / d as f64 - r, i))
        },
        (Ok(Complex(lr, i)), &Integer(r)) => Ok(Complex(lr - r as f64, i)),
        (Ok(Complex(lr, i)), &Real(r)) => Ok(Complex(lr - r, i)),
        (Ok(Complex(lr, i)), &Rational(n, d)) => {
          Ok(Complex(lr - n as f64 / d as f64, i))
        },
        (Ok(Complex(lr, li)), &Complex(rr, ri)) => {
          Ok(Complex(lr - rr, li - ri))
        },

        (Err(l), _) => Err(l),
        (Ok(_), r) => {
          Err(Box::new(ArithmeticError::NonNumericArgument(r.clone())))
        },
      })
    }
  });

  vm.def_builtin("/", 2, true, |vm, xs| {
    if xs.len() == 0 {
      Err(Box::new(UnspecifiedError))
    } else if xs.len() == 1 {
      return match xs[0].data {
        Integer(x) => Ok(Real(1.0 / x as f64)),
        Real(x) => Ok(Real(1.0 / x)),
        Rational(n, d) => Ok(vm.rational(d, n)),
        Complex(r, i) => Ok(Complex(1.0 / r, 1.0 / i)),
        ref x => Err(Box::new(ArithmeticError::NonNumericArgument(x.clone()))),
      };
    } else {
      let mut xs_iter = xs.iter();
      let next_arg = xs_iter.next().unwrap();
      let dividend = match next_arg.data.clone_numeric() {
        Ok(data) => data,
        Err(e) => {
          return Err(Box::new(e));
        },
      };
      xs_iter.fold(Ok(dividend), |a, x| match (a, &x.data) {
        (Ok(Integer(l)), &Integer(r)) => Ok(Real(l as f64 / r as f64)),
        (Ok(Integer(l)), &Real(r)) => Ok(Real(l as f64 / r)),
        (Ok(Integer(l)), &Rational(n, d)) => Ok(Rational(l * d as i64, n)),
        (Ok(Integer(l)), &Complex(r, i)) => {
          Ok(Complex(l as f64 / r, l as f64 / i))
        },
        (Ok(Real(l)), &Integer(r)) => Ok(Real(l / r as f64)),
        (Ok(Real(l)), &Real(r)) => Ok(Real(l / r)),
        (Ok(Real(l)), &Rational(n, d)) => Ok(Real(l / n as f64 * d as f64)),
        (Ok(Real(l)), &Complex(r, i)) => Ok(Complex(l / r, l / i)),
        (Ok(Rational(n, d)), &Integer(r)) => Ok(vm.rational(n, d * r)),
        (Ok(Rational(n, d)), &Real(r)) => Ok(Real(n as f64 / d as f64 / r)),
        (Ok(Rational(ln, ld)), &Rational(rn, rd)) => {
          Ok(vm.rational(ln * rd, ld * rn))
        },
        (Ok(Rational(n, d)), &Complex(r, i)) => {
          let rat = n as f64 / d as f64;
          Ok(Complex(rat / r, rat / i))
        },

        (Ok(Complex(lr, i)), &Integer(r)) => {
          Ok(Complex(lr / r as f64, i / r as f64))
        },
        (Ok(Complex(lr, i)), &Real(r)) => Ok(Complex(lr / r, i / r)),
        (Ok(Complex(lr, i)), &Rational(n, d)) => {
          let rat = n as f64 / d as f64;
          Ok(Complex(lr / rat, i / rat))
        },
        (Ok(Complex(lr, li)), &Complex(rr, ri)) => {
          let real = lr / rr + li / ri;
          let imag = lr / ri + li / rr;
          Ok(Complex(real, imag))
        },

        (Err(l), _) => Err(l),
        (Ok(_), r) => {
          Err(Box::new(ArithmeticError::NonNumericArgument(r.clone())))
        },
      })
    }
  });
}

#[cfg(test)]
mod tests {
  use crate::{data::Data, vm::VM};

  #[test]
  fn number_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(number? 5i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let real = vm.eval_str("(number? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let rational = vm.eval_str("(number? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(number? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(number? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(number? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn complex_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(complex? 5i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let real = vm.eval_str("(complex? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let rational = vm.eval_str("(complex? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(complex? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(complex? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(complex? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn real_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(real? 0i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let complex2 = vm.eval_str("(real? 1.0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex2.data);
    }

    {
      let real = vm.eval_str("(real? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let rational = vm.eval_str("(real? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(real? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(real? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(real? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn rational_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(rational? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let complex2 = vm.eval_str("(rational? 5.3+0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex2.data);
    }

    {
      let complex3 = vm.eval_str("(rational? 5+1i)").unwrap();
      assert_eq!(Data::Boolean(false), complex3.data);
    }

    {
      let real = vm.eval_str("(rational? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let real2 = vm.eval_str("(rational? 5.3)").unwrap();
      assert_eq!(Data::Boolean(false), real2.data);
    }

    {
      let rational = vm.eval_str("(rational? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(rational? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(rational? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(rational? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn integer_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(integer? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let complex2 = vm.eval_str("(integer? 5.3+0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex2.data);
    }

    {
      let complex3 = vm.eval_str("(integer? 5+1i)").unwrap();
      assert_eq!(Data::Boolean(false), complex3.data);
    }

    {
      let real = vm.eval_str("(integer? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let real2 = vm.eval_str("(integer? 5.3)").unwrap();
      assert_eq!(Data::Boolean(false), real2.data);
    }

    {
      let rational = vm.eval_str("(integer? 2/3)").unwrap();
      assert_eq!(Data::Boolean(false), rational.data);
    }

    {
      let rational2 = vm.eval_str("(integer? 4/2)").unwrap();
      assert_eq!(Data::Boolean(true), rational2.data);
    }

    {
      let integer = vm.eval_str("(integer? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(integer? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(integer? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn exact_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(exact? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex.data);
    }

    {
      let real = vm.eval_str("(exact? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), real.data);
    }

    {
      let rational = vm.eval_str("(exact? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(exact? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(exact? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(exact? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn inexact_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(inexact? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let real = vm.eval_str("(inexact? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let rational = vm.eval_str("(inexact? 2/3)").unwrap();
      assert_eq!(Data::Boolean(false), rational.data);
    }

    {
      let integer = vm.eval_str("(inexact? 5)").unwrap();
      assert_eq!(Data::Boolean(false), integer.data);
    }

    {
      let string = vm.eval_str("(inexact? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(inexact? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn exact_integer_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(exact-integer? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex.data);
    }

    {
      let real = vm.eval_str("(exact-integer? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), real.data);
    }

    {
      let rational = vm.eval_str("(exact-integer? 2/3)").unwrap();
      assert_eq!(Data::Boolean(false), rational.data);
    }

    {
      let rational2 = vm.eval_str("(exact-integer? 3/1)").unwrap();
      assert_eq!(Data::Boolean(true), rational2.data);
    }

    {
      let integer = vm.eval_str("(exact-integer? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(exact-integer? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(exact-integer? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn finite_test() {
    let mut vm = VM::new();

    {
      let inf = vm.eval_str("(finite? Inf)").unwrap();
      assert_eq!(Data::Boolean(false), inf.data);
    }

    {
      let neg_inf = vm.eval_str("(finite? -Inf)").unwrap();
      assert_eq!(Data::Boolean(false), neg_inf.data);
    }

    {
      let complex = vm.eval_str("(finite? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), complex.data);
    }

    {
      let real = vm.eval_str("(finite? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), real.data);
    }

    {
      let rational = vm.eval_str("(finite? 2/3)").unwrap();
      assert_eq!(Data::Boolean(true), rational.data);
    }

    {
      let integer = vm.eval_str("(finite? 5)").unwrap();
      assert_eq!(Data::Boolean(true), integer.data);
    }

    {
      let string = vm.eval_str("(finite? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(finite? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn infinite_test() {
    let mut vm = VM::new();

    {
      let inf = vm.eval_str("(infinite? Inf)").unwrap();
      assert_eq!(Data::Boolean(true), inf.data);
    }

    {
      let neg_inf = vm.eval_str("(infinite? -Inf)").unwrap();
      assert_eq!(Data::Boolean(true), neg_inf.data);
    }

    {
      let complex = vm.eval_str("(infinite? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), complex.data);
    }

    {
      let real = vm.eval_str("(infinite? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), real.data);
    }

    {
      let rational = vm.eval_str("(infinite? 2/3)").unwrap();
      assert_eq!(Data::Boolean(false), rational.data);
    }

    {
      let integer = vm.eval_str("(infinite? 5)").unwrap();
      assert_eq!(Data::Boolean(false), integer.data);
    }

    {
      let string = vm.eval_str("(infinite? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), string.data);
    }

    {
      let nil = vm.eval_str("(infinite? '())").unwrap();
      assert_eq!(Data::Boolean(false), nil.data);
    }
  }

  #[test]
  fn addition() {
    let mut vm = VM::new();

    {
      let integer = vm.eval_str("(+ 5 5)").unwrap();
      assert_eq!(Data::Integer(10), integer.data);
    }

    {
      let rational = vm.eval_str("(+ 5 10/2)").unwrap();
      assert_eq!(Data::Rational(10, 1), rational.data);
    }

    {
      let real = vm.eval_str("(+ 5 5.0)").unwrap();
      assert_eq!(Data::Real(10.0), real.data);
    }

    {
      let complex = vm.eval_str("(+ 1 i)").unwrap();
      assert_eq!(Data::Complex(1.0, 1.0), complex.data);
    }
  }

  #[test]
  fn multiplication() {
    let mut vm = VM::new();

    {
      let integer = vm.eval_str("(* 5 5)").unwrap();
      assert_eq!(Data::Integer(25), integer.data);
    }

    {
      let rational = vm.eval_str("(* 5 10/2)").unwrap();
      assert_eq!(Data::Rational(25, 1), rational.data);
    }

    {
      let real = vm.eval_str("(* 5 5.0)").unwrap();
      assert_eq!(Data::Real(25.0), real.data);
    }

    {
      let complex = vm.eval_str("(* 1 i)").unwrap();
      assert_eq!(Data::Complex(0.0, 1.0), complex.data);
    }
  }

  #[test]
  fn subtraction() {
    let mut vm = VM::new();

    {
      let integer = vm.eval_str("(- 5 5)").unwrap();
      assert_eq!(Data::Integer(0), integer.data);
    }

    {
      let rational = vm.eval_str("(- 5 10/2)").unwrap();
      assert_eq!(Data::Rational(0, 1), rational.data);
    }

    {
      let real = vm.eval_str("(- 5 5.0)").unwrap();
      assert_eq!(Data::Real(0.0), real.data);
    }

    {
      let complex = vm.eval_str("(- 1 i)").unwrap();
      assert_eq!(Data::Complex(1.0, -1.0), complex.data);
    }
  }

  #[test]
  fn division() {
    let mut vm = VM::new();

    {
      let integer = vm.eval_str("(/ 5 5)").unwrap();
      assert_eq!(Data::Real(1.0), integer.data);
    }

    {
      let rational = vm.eval_str("(/ 5 10/2)").unwrap();
      assert_eq!(Data::Rational(1, 1), rational.data);
    }

    {
      let real = vm.eval_str("(/ 5 5.0)").unwrap();
      assert_eq!(Data::Real(1.0), real.data);
    }

    {
      let complex = vm.eval_str("(/ i 1)").unwrap();
      assert_eq!(Data::Complex(0.0, 1.0), complex.data);
    }
  }
}
