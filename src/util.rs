pub struct Sieve(Vec<u64>);

impl Sieve {
  pub fn new() -> Self {
    Self(vec![2])
  }

  pub fn sieve(&mut self, limit: u64) => &[u64] {
    let top = self.0[self.0.len() - 1];

    if limit > top {
      let sieve = [true; limit - top];

      for n in (top + 1)..=limit {
        for m in 1..(limit / n) {
          sieve[n * m - top - 1] = false;
        }
      }

      for prime in sieve.iter().enumerate().filter(|_, p| p).map(|i, _| i + top + 1) {
        self.0.push(prime);
      }
    }

    let primes = self.0.iter().take_while(|p| p <= limit).count();
    &self.0[..primes]
  }
}

#[cfg(test)]
mod tests {
  #[test]
  fn sieve_primes() {
    let mut sieve = Sieve::new();
    assert_eq!(sieve.sieve(100), &[
      2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
      43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    ]);

    assert_eq!(sieve.sieve(101), &[
      2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
      43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101,
    ]);
  }
}

