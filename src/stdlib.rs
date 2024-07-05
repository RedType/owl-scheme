use crate::{data::Data, error::UnspecifiedError, vm::VM};

pub fn import_std(vm: &mut VM) {
  use Data::*;

  vm.def_builtin("number?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("complex?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("real?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, i) => i == 0.0,
        Real(_) | Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("rational?", |args| {
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

  vm.def_builtin("integer?", |args| {
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

  vm.def_builtin("exact?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Rational(_, _) | Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("inexact?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(_, _) | Real(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("exact-integer?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Rational(_, d) => d == 1,
        Integer(_) => true,
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("finite?", |args| {
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

  vm.def_builtin("infinite?", |args| {
    let res = args.iter().fold(true, |a, x| {
      a && match *x.borrow() {
        Complex(r, i) => r.is_infinite() || i.is_infinite(),
        Real(n) => n.is_infinite(),
        _ => false,
      }
    });
    Ok(Boolean(res))
  });

  vm.def_builtin("+", |xs| {
    let res = xs.iter().fold(Integer(0), |a, x| match (a, &*x.borrow()) {
      (Integer(l), &Integer(r)) => Integer(l + r),
      (Integer(i), &Rational(n, d)) | (Rational(n, d), &Integer(i)) => {
        Rational(i * d as i64 + n, d)
      }
      (Integer(i), &Real(r)) | (Real(r), &Integer(i)) => Real(r + i as f64),
      (Integer(n), &Complex(r, i)) | (Complex(r, i), &Integer(n)) => Complex(r + n as f64, i),
      (Rational(ln, ld), &Rational(rn, rd)) => {
        let n = ln * rd as i64 + rn * ld as i64;
        let d = ld * rd;
        Rational(n, d)
      }
      (Rational(n, d), &Real(r)) | (Real(r), &Rational(n, d)) => Real((n as f64 / d as f64) + r),
      (Rational(n, d), &Complex(r, i)) | (Complex(r, i), &Rational(n, d)) => {
        Complex(n as f64 / d as f64 + r, i)
      }
      (Real(l), &Real(r)) => Real(l + r),
      (Real(n), &Complex(r, i)) | (Complex(r, i), &Real(n)) => Complex(n + r, i),
      (Complex(lr, li), &Complex(rr, ri)) => Complex(lr + rr, li + ri),

      _ => Data::nil(),
    });
    if res.is_nil() {
      Err(Box::new(UnspecifiedError))
    } else {
      Ok(res)
    }
  });

  vm.def_builtin("*", |xs| {
    let res = xs.iter().fold(Integer(1), |a, x| match (a, &*x.borrow()) {
      (Integer(l), &Integer(r)) => Integer(l * r),
      (Integer(i), &Rational(n, d)) | (Rational(n, d), &Integer(i)) => Rational(i * n, d),
      (Integer(i), &Real(r)) | (Real(r), &Integer(i)) => Real(r * i as f64),
      (Integer(n), &Complex(r, i)) | (Complex(r, i), &Integer(n)) => {
        Complex(r * n as f64, i * n as f64)
      }
      (Rational(ln, ld), &Rational(rn, rd)) => Rational(ln * rn, ld * rd),
      (Rational(n, d), &Real(r)) | (Real(r), &Rational(n, d)) => Real((n as f64 / d as f64) * r),
      (Rational(n, d), &Complex(r, i)) | (Complex(r, i), &Rational(n, d)) => {
        let rat = n as f64 / d as f64;
        Complex(rat * r, rat * i)
      }
      (Real(l), &Real(r)) => Real(l * r),
      (Real(n), &Complex(r, i)) | (Complex(r, i), &Real(n)) => Complex(n * r, n * i),
      (Complex(lr, li), &Complex(rr, ri)) => Complex(lr * rr - li * ri, lr * ri + li * rr),

      _ => Data::nil(),
    });
    if res.is_nil() {
      Err(Box::new(UnspecifiedError))
    } else {
      Ok(res)
    }
  });

  vm.def_builtin("-", |xs| {
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

  vm.def_builtin("/", |xs| {
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
        }
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
