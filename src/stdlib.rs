use crate::{
  data::{Data, DataCell},
  error::UnspecifiedError,
  vm::VM,
};
use std::f64::consts;

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
  vm.def_builtin("number?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("complex?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("real?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, i) => i == 0.0,
        Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("rational?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(r, i) => i == 0.0 && r.round() == r,
        Real(n) => n.round() == n,
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("integer?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(r, i) => i == 0.0 && r.round() == r,
        Real(n) => n.round() == n,
        Rational(_, d) => d == 1,
        Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("exact?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("inexact?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("exact-integer?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Rational(_, d) => d == 1,
        Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("finite?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(r, i) => r.is_finite() && i.is_finite(),
        Real(n) => n.is_finite(),
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("infinite?", 1, |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(r, i) => r.is_infinite() || i.is_infinite(),
        Real(n) => n.is_infinite(),
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("+", 2, |xs| {
    let res = xs.iter().fold(Integer(0), |a, x| match (a, &*x.borrow()) {
      (Integer(l), &Integer(r)) => Integer(l + r),
      (Integer(i), &Rational(n, d)) | (Rational(n, d), &Integer(i)) => {
        Rational(i * d as i64 + n, d)
      },
      (Integer(i), &Real(r)) | (Real(r), &Integer(i)) => Real(r + i as f64),
      (Integer(n), &Complex(r, i)) | (Complex(r, i), &Integer(n)) => {
        Complex(r + n as f64, i)
      },
      (Rational(ln, ld), &Rational(rn, rd)) => {
        let n = ln * rd as i64 + rn * ld as i64;
        let d = ld * rd;
        Rational(n, d)
      },
      (Rational(n, d), &Real(r)) | (Real(r), &Rational(n, d)) => {
        Real((n as f64 / d as f64) + r)
      },
      (Rational(n, d), &Complex(r, i)) | (Complex(r, i), &Rational(n, d)) => {
        Complex(n as f64 / d as f64 + r, i)
      },
      (Real(l), &Real(r)) => Real(l + r),
      (Real(n), &Complex(r, i)) | (Complex(r, i), &Real(n)) => {
        Complex(n + r, i)
      },
      (Complex(lr, li), &Complex(rr, ri)) => Complex(lr + rr, li + ri),

      _ => Data::nil(),
    });
    if res.is_nil() {
      Err(Box::new(UnspecifiedError))
    } else {
      Ok(res)
    }
  });

  vm.def_builtin("*", 2, |xs| {
    let res = xs.iter().fold(Integer(1), |a, x| match (a, &*x.borrow()) {
      (Integer(l), &Integer(r)) => Integer(l * r),
      (Integer(i), &Rational(n, d)) | (Rational(n, d), &Integer(i)) => {
        Rational(i * n, d)
      },
      (Integer(i), &Real(r)) | (Real(r), &Integer(i)) => Real(r * i as f64),
      (Integer(n), &Complex(r, i)) | (Complex(r, i), &Integer(n)) => {
        Complex(r * n as f64, i * n as f64)
      },
      (Rational(ln, ld), &Rational(rn, rd)) => Rational(ln * rn, ld * rd),
      (Rational(n, d), &Real(r)) | (Real(r), &Rational(n, d)) => {
        Real((n as f64 / d as f64) * r)
      },
      (Rational(n, d), &Complex(r, i)) | (Complex(r, i), &Rational(n, d)) => {
        let rat = n as f64 / d as f64;
        Complex(rat * r, rat * i)
      },
      (Real(l), &Real(r)) => Real(l * r),
      (Real(n), &Complex(r, i)) | (Complex(r, i), &Real(n)) => {
        Complex(n * r, n * i)
      },
      (Complex(lr, li), &Complex(rr, ri)) => {
        Complex(lr * rr - li * ri, lr * ri + li * rr)
      },

      _ => Data::nil(),
    });
    if res.is_nil() {
      Err(Box::new(UnspecifiedError))
    } else {
      Ok(res)
    }
  });

  vm.def_builtin("-", 2, |xs| {
    if xs.len() == 0 {
      Err(Box::new(UnspecifiedError))
    } else if xs.len() == 1 {
      return match &*xs[0].borrow() {
        &Integer(x) => Ok(Integer(-x)),
        &Real(x) => Ok(Real(-x)),
        _ => Err(Box::new(UnspecifiedError)),
      };
    } else {
      let mut xs_iter = xs.iter();
      let minuend = xs_iter.next().unwrap().borrow().clone_numeric()?;
      let res = xs_iter.fold(minuend, |a, x| match (a, &*x.borrow()) {
        (Integer(l), &Integer(r)) => Integer(l - r),
        (Real(l), &Integer(r)) => Real(l - r as f64),
        (Integer(l), &Real(r)) => Real(l as f64 - r),
        (Real(l), &Real(r)) => Real(l - r),
        _ => Data::nil(),
      });
      if res.is_nil() {
        Err(Box::new(UnspecifiedError))
      } else {
        Ok(res)
      }
    }
  });

  vm.def_builtin("/", 2, |xs| {
    if xs.len() == 0 {
      Err(Box::new(UnspecifiedError))
    } else if xs.len() == 1 {
      return match &*xs[0].borrow() {
        &Integer(x) => Ok(Real(1.0 / x as f64)),
        &Real(x) => Ok(Real(1.0 / x)),
        _ => Err(Box::new(UnspecifiedError)),
      };
    } else {
      let mut xs_iter = xs.iter();
      let next_arg = xs_iter.next().unwrap();
      let dividend = match next_arg.borrow().clone_numeric() {
        Ok(data) => data,
        Err(e) => {
          return Err(Box::new(e));
        },
      };
      let res = xs_iter.fold(dividend, |a, x| match (a, &*x.borrow()) {
        (Integer(l), &Integer(r)) => Real(l as f64 / r as f64),
        (Real(l), &Integer(r)) => Real(l / r as f64),
        (Integer(l), &Real(r)) => Real(l as f64 / r),
        (Real(l), &Real(r)) => Real(l / r),
        _ => Data::nil(),
      });
      if res.is_nil() {
        Err(Box::new(UnspecifiedError))
      } else {
        Ok(res)
      }
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
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let real = vm.eval_str("(number? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let rational = vm.eval_str("(number? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(number? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(number? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(number? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn complex_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(complex? 5i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let real = vm.eval_str("(complex? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let rational = vm.eval_str("(complex? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(complex? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(complex? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(complex? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn real_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(real? 0i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let complex2 = vm.eval_str("(real? 1.0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex2.borrow());
    }

    {
      let real = vm.eval_str("(real? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let rational = vm.eval_str("(real? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(real? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(real? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(real? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn rational_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(rational? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let complex2 = vm.eval_str("(rational? 5.3+0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex2.borrow());
    }

    {
      let complex3 = vm.eval_str("(rational? 5+1i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex3.borrow());
    }

    {
      let real = vm.eval_str("(rational? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let real2 = vm.eval_str("(rational? 5.3)").unwrap();
      assert_eq!(Data::Boolean(false), *real2.borrow());
    }

    {
      let rational = vm.eval_str("(rational? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(rational? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(rational? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(rational? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn integer_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(integer? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let complex2 = vm.eval_str("(integer? 5.3+0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex2.borrow());
    }

    {
      let complex3 = vm.eval_str("(integer? 5+1i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex3.borrow());
    }

    {
      let real = vm.eval_str("(integer? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let real2 = vm.eval_str("(integer? 5.3)").unwrap();
      assert_eq!(Data::Boolean(false), *real2.borrow());
    }

    {
      let rational = vm.eval_str("(integer? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(false), *rational.borrow());
    }

    {
      let rational2 = vm.eval_str("(integer? (/ 2 1))").unwrap();
      assert_eq!(Data::Boolean(true), *rational2.borrow());
    }

    {
      let integer = vm.eval_str("(integer? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(integer? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(integer? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn exact_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(exact? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex.borrow());
    }

    {
      let real = vm.eval_str("(exact? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), *real.borrow());
    }

    {
      let rational = vm.eval_str("(exact? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(exact? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(exact? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(exact? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn inexact_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(inexact? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let real = vm.eval_str("(inexact? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let rational = vm.eval_str("(inexact? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(false), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(inexact? 5)").unwrap();
      assert_eq!(Data::Boolean(false), *integer.borrow());
    }

    {
      let string = vm.eval_str("(inexact? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(inexact? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn exact_integer_test() {
    let mut vm = VM::new();

    {
      let complex = vm.eval_str("(exact-integer? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex.borrow());
    }

    {
      let real = vm.eval_str("(exact-integer? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), *real.borrow());
    }

    {
      let rational = vm.eval_str("(exact-integer? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(false), *rational.borrow());
    }

    {
      let rational2 = vm.eval_str("(exact-integer? (/ 2 1))").unwrap();
      assert_eq!(Data::Boolean(true), *rational2.borrow());
    }

    {
      let integer = vm.eval_str("(exact-integer? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(exact-integer? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(exact-integer? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn finite_test() {
    let mut vm = VM::new();

    {
      let inf = vm.eval_str("(finite? Inf)").unwrap();
      assert_eq!(Data::Boolean(false), *inf.borrow());
    }

    {
      let neg_inf = vm.eval_str("(finite? -Inf)").unwrap();
      assert_eq!(Data::Boolean(false), *neg_inf.borrow());
    }

    {
      let complex = vm.eval_str("(finite? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(true), *complex.borrow());
    }

    {
      let real = vm.eval_str("(finite? 5.0)").unwrap();
      assert_eq!(Data::Boolean(true), *real.borrow());
    }

    {
      let rational = vm.eval_str("(finite? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(true), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(finite? 5)").unwrap();
      assert_eq!(Data::Boolean(true), *integer.borrow());
    }

    {
      let string = vm.eval_str("(finite? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(finite? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn infinite_test() {
    let mut vm = VM::new();

    {
      let inf = vm.eval_str("(infinite? Inf)").unwrap();
      assert_eq!(Data::Boolean(true), *inf.borrow());
    }

    {
      let neg_inf = vm.eval_str("(infinite? -Inf)").unwrap();
      assert_eq!(Data::Boolean(true), *neg_inf.borrow());
    }

    {
      let complex = vm.eval_str("(infinite? 5+0i)").unwrap();
      assert_eq!(Data::Boolean(false), *complex.borrow());
    }

    {
      let real = vm.eval_str("(infinite? 5.0)").unwrap();
      assert_eq!(Data::Boolean(false), *real.borrow());
    }

    {
      let rational = vm.eval_str("(infinite? (/ 2 3))").unwrap();
      assert_eq!(Data::Boolean(false), *rational.borrow());
    }

    {
      let integer = vm.eval_str("(infinite? 5)").unwrap();
      assert_eq!(Data::Boolean(false), *integer.borrow());
    }

    {
      let string = vm.eval_str("(infinite? \"hello\")").unwrap();
      assert_eq!(Data::Boolean(false), *string.borrow());
    }

    {
      let nil = vm.eval_str("(infinite? '())").unwrap();
      assert_eq!(Data::Boolean(false), *nil.borrow());
    }
  }

  #[test]
  fn addition() {
    let mut vm = VM::new();

    {
      let integer = vm.eval_str("(+ 5 5)").unwrap();
      assert_eq!(Data::Integer(10), *integer.borrow());
    }

    {
      let rational = vm.eval_str("(+ 5 (/ 10 2))").unwrap();
      assert_eq!(Data::Rational(10, 1), *rational.borrow());
    }

    {
      let real = vm.eval_str("(+ 5 5.0)").unwrap();
      assert_eq!(Data::Real(10.0), *real.borrow());
    }

    {
      let complex = vm.eval_str("(+ 1 i)").unwrap();
      assert_eq!(Data::Complex(1.0, 1.0), *complex.borrow());
    }
  }
}
