use std::iter;
use crate::{
  data::Data,
  vm::VM,
};

macro_rules! builtin {
  ($vm:ident, $name:expr, $f:expr) => {
    $vm.def_builtin($name, |data| if let List(xs) = data {
      // fetch iterator and effective length of argument list (without trailing nil)
      let (mut iter, len) = if xs.back().borrow().is_nil() {
        (xs.iter().take(xs.len() - 1), xs.len() - 1)
      } else {
        (xs.iter(), xs.len())
      };
      $f($vm, iter, len)
    } else if let Nil = data {
      $f($vm, iter::empty(), 0)
    } else {
      panic!("Failed precondition: builtins must be passed an argument list")
    })
  };
}

fn import_std(vm: &mut VM) {
  use Data::*;

  builtin!(vm, "number?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "complex?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(_, _) | Real(_) | Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "real?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(_, i) => i == 0.0,
      Real(_) | Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "rational?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(r, i) => i == 0.0 && r.round() == r,
      Real(n) => n.round() == n,
      Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "integer?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(r, i) => i == 0.0 && r.round() == r,
      Real(n) => n.round() == n,
      Rational(_, d) => d == 1,
      Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "exact?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "inexact?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(_, _) | Real(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "exact-integer?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Rational(_, d) => d == 1,
      Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "finite?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(r, i) => r.is_finite() && i.is_finite(),
      Real(n) => n.is_finite(),
      Rational(_, _) | Integer(_) => true,
      _ => false,
    })))
  });

  builtin!(vm, "infinite?", |_, args, _| {
    Ok(Boolean(args.fold(true, |a, x| a && match x {
      Complex(r, i) => r.is_infinite() || i.is_infinite(),
      Real(n) => n.is_infinite(),
      _ => false,
    })))
  });

  builtin!(vm, "+", |vm, xs, _| {
    let res = xs.fold(Integer(0), |a, x| match (a, x.borrow()) {
      (Integer(l), Integer(r)) =>
        Integer(l + r),
      (Integer(i), Rational(n, d)) | (Rational(n, d), Integer(i)) =>
        Rational(i * d + n, d),
      (Integer(i), Real(r)) | (Real(r), Integer(i)) =>
        Real(r + i as f64),
      (Integer(n), Complex(r, i)) | (Complex(r, i), Integer(n)) =>
        Complex(r + n, i),
      (Rational(ln, ld), Rational(rn, rd)) => {
        let n = ln * rd as i64 + rn * ld as i64;
        let d = ld * rd;
        vm.rat(n, d as i64)
      },
      (Rational(n, d), Real(r)) | (Real(r), Rational(n, d)) =>
        Rational(r * d + n, d),
      (Rational(n, d), Complex(r, i)) | (Complex(r, i), Rational(n, d)) =>
        Complex(n as f64 / d as f64 + r, i),
      (Real(l), Real(r)) =>
        Real(l + r),
      (Real(n), Complex(r, i)) | (Complex(r, i), Real(n)) =>
        Complex(n + r, i),
      (Complex(lr, li), Complex(rr, ri)) =>
        Complex(lr + rr, li + ri),
        
      _ => Nil,
    });
    if let Nil = res { Err(()) } else { Ok(res) }
  });

  builtin!(vm, "*", |xs, _| {
    let res = xs.fold(Integer(1), |a, x| match (a, x.borrow()) {
      (Integer(l), Integer(r)) =>
        Integer(l * r),
      (Integer(i), Rational(n, d)) | (Rational(n, d), Integer(i)) =>
        Rational(i * n, d),
      (Integer(i), Real(r)) | (Real(r), Integer(i)) =>
        Real(r * i as f64),
      (Integer(n), Complex(r, i)) | (Complex(r, i), Integer(n)) =>
        Complex(r as f64 * n, r as f64 * i),
      (Rational(ln, ld), Rational(rn, rd)) =>
        vm.rat(ln * rn, (ld * rd) as i64),
      (Rational(n, d), Real(r)) | (Real(r), Rational(n, d)) =>
        Rational(r * n, d),
      (Rational(n, d), Complex(r, i)) | (Complex(r, i), Rational(n, d)) => {
        let rat = n as f64 / d as f64;
        Complex(rat * r, rat * i)
      },
      (Real(l), Real(r)) =>
        Real(l * r),
      (Real(n), Complex(r, i)) | (Complex(r, i), Real(n)) =>
        Complex(n * r, n * i),
      (Complex(lr, li), Complex(rr, ri)) =>
        Complex(lr * rr - li * ri, lr * ri + li * rr),
        
      _ => Nil,
    });
    if let Nil = res { Err(()) } else { Ok(res) }
  });

  builtin!(vm, "-", |xs, len| {
    if len == 0 {
      Err(())
    } else if len == 1 {
      return match xs.next() {
        Integer(x) => Ok(Integer(-x)),
        Float(x) => Ok(Float(-x)),
        _ => Err(()),
      };
    } else {
      let minuend = xs.next();
      let res = xs.fold(minuend.borrow(), |a, x| match (a, x.borrow()) {
        (Integer(l), Integer(r)) => Integer(l - r),
        (Float(l), Integer(r)) => Float(l - r as f64),
        (Integer(l), Float(r)) => Float(l as f64 - r),
        (Float(l), Float(r)) => Float(l - r),
        _ => Nil,
      });
      if let Nil = res { Err(()) } else { Ok(res) }
    }
  });

  builtin!(vm, "/", |xs, len| {
    if len == 0 {
      Err(())
    } else if len == 1 {
      return match xs.next() {
        Integer(x) => Ok(Float(1 / x as f64)),
        Float(x) => Ok(Float(1 / x)),
        _ => Err(()),
      };
    } else {
      let dividend = xs.next();
      let res = xs.fold(dividend.borrow(), |a, x| match (a, x.borrow()) {
        (Integer(l), Integer(r)) => Float(l as f64 / r as f64),
        (Float(l), Integer(r)) => Float(l / r as f64),
        (Integer(l), Float(r)) => Float(l as f64 / r),
        (Float(l), Float(r)) => Float(l / r),
        _ => Nil,
      });
      if let Nil = res { Err(()) } else { Ok(res) }
    }
  });
}

