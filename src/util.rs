use std::{
  cell::RefCell,
  collections::HashMap,
  rc::{Rc, Weak},
};
use log::*;

#[derive(Debug)]
pub struct Sieve(Vec<usize>);

impl Sieve {
  pub fn new() -> Self {
    Self(vec![2])
  }

  pub fn sieve(&mut self, limit: usize) -> &[usize] {
    let top = self.0[self.0.len() - 1];

    if limit > top {
      let sieve = vec![true; limit - top];

      for n in (top + 1)..=limit {
        for m in 1..(limit / n) {
          sieve[(n * m - top - 1)] = false;
        }
      }

      for prime in sieve.iter().enumerate().filter(|(_, p)| **p).map(|(i, _)| i + top + 1) {
        self.0.push(prime);
      }
    }

    let primes = self.0.iter().take_while(|p| **p <= limit).count();
    &self.0[..primes]
  }
}

#[derive(Debug)]
struct LRUNode {
  n: usize,
  prev: Option<Weak<RefCell<LRUNode>>>,
  next: Option<Rc<RefCell<LRUNode>>>,
}

#[derive(Debug)]
pub struct LRU {
  index: HashMap<usize, Rc<RefCell<LRUNode>>>,
  head: Option<Rc<RefCell<LRUNode>>>,
  tail: Option<Rc<RefCell<LRUNode>>>,
}

impl LRU {
  pub fn with_capacity(n: usize) -> Self {
    Self {
      index: HashMap::with_capacity(n),
      head: None,
      tail: None,
    }
  }

  pub fn len(&self) -> usize {
    self.index.len()
  }

  pub fn enqueue(&mut self, n: usize) {
    if self.index.contains_key(&n) {
      warn!("Attempted to enqueue already-existing cache element {}", n);
      self.touch(n);
      return;
    }

    let mut new_head = Rc::new(RefCell::new(LRUNode {
      n,
      prev: None,
      next: self.head.as_ref().map(|h| Rc::clone(h)),
    }));

    if let Some(h) = self.head {
      h.borrow_mut().prev = Some(Rc::downgrade(&new_head));
    } else {
      self.tail = Some(Rc::clone(&new_head));
    }

    self.head = Some(Rc::clone(&new_head));

    self.index.insert(n, new_head);
  }

  pub fn dequeue(&mut self) -> Option<usize> {
    if let Some(tail) = self.tail {
      if let Some(prev) = tail.borrow_mut().prev.as_ref().map(|p| Weak::upgrade(p).unwrap()) {
        prev.borrow_mut().next = None;
        self.tail = Some(prev);
      } else { // tail is our last element
        self.head = None;
        self.tail = None;
      }
      self.index.remove(&tail.borrow().n);
      Some(tail.borrow().n)
    } else { // list is empty
      None
    }
  }

  pub fn touch(&mut self, n: usize) {
    if let Some(node) = self.index.get(&n).as_ref().map(|node| Rc::clone(node)) {
      // unlink node
      if let Some(prev) = node.borrow_mut().prev.as_ref().map(|p| Weak::upgrade(p).unwrap()) {
        if let Some(next) = node.borrow_mut().next {
          prev.borrow_mut().next = Some(Rc::clone(&next));
          next.borrow_mut().prev = Some(Rc::downgrade(&prev));
        } else { // node is tail
          prev.borrow_mut().next = None;
          self.tail = Some(Rc::clone(&prev));
        }
      } else { // node is head
        return; // no work to do
      }

      // relink node
      if let Some(head) = self.head.as_ref().map(|h| Rc::clone(h)) {
        node.borrow_mut().next = Some(Rc::clone(&head));
        self.head = Some(Rc::clone(&node));
      } else { // there is no head
        unreachable!(); // data structure is in an inconsistent state
      }
    } else { // no such element was encountered
      warn!("Attempted to touch {}, which was not in the LRU cache", n);
      self.enqueue(n);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

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

  #[test]
  fn lru_cache_eviction_strategy() {
    let mut queue = LRU::with_capacity(10);

    assert_eq!(queue.dequeue(), None);

    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);
    assert_eq!(queue.len(), 3);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.len(), 2);
    assert_eq!(queue.dequeue(), Some(3));
    assert_eq!(queue.len(), 1);
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);
    queue.touch(2);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.dequeue(), Some(3));
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.touch(1);
    assert_eq!(queue.len(), 1);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.enqueue(2);
    queue.touch(1);
    queue.touch(2);
    assert_eq!(queue.len(), 2);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 0);
  }
}

