use log::*;
use std::{
  collections::HashMap,
  fmt::Debug,
  hash::{DefaultHasher, Hash, Hasher},
  marker::PhantomData,
  ptr::NonNull,
};

#[derive(Debug)]
pub struct LRU<T: Debug + Hash> {
  index: HashMap<u64, NonNull<LRUNode<T>>>,
  head: Option<NonNull<LRUNode<T>>>,
  tail: Option<NonNull<LRUNode<T>>>,
  phantom: PhantomData<T>,
}

#[derive(Debug)]
struct LRUNode<T: Debug + Hash> {
  elem: T,
  prev: Option<NonNull<LRUNode<T>>>,
  next: Option<NonNull<LRUNode<T>>>,
}

impl<T: Debug + Hash> LRU<T> {
  pub fn with_capacity(n: usize) -> Self {
    Self {
      index: HashMap::with_capacity(n),
      head: None,
      tail: None,
      phantom: PhantomData,
    }
  }

  pub fn len(&self) -> usize {
    self.index.len()
  }

  pub fn enqueue(&mut self, elem: T) {
    let hash = hash(&elem);
    if self.index.contains_key(&hash) {
      warn!(
        "Attempted to enqueue already-existing cache element {:?}",
        elem
      );
      self.touch(&elem);
      return;
    }

    let new_head = Box::new(LRUNode {
      elem,
      prev: None,
      next: None,
    });
    let new_head_ptr = NonNull::from(Box::leak(new_head));

    self.index.insert(hash, new_head_ptr);

    // push node to front
    unsafe {
      self.push_node(new_head_ptr);
    }
  }

  pub fn touch(&mut self, elem: &T) {
    let hash = hash(&elem);

    if let Some(&node) = self.index.get(&hash) {
      unsafe {
        // cut node out of list
        self.unlink_node(node);
        // push to front
        self.push_node(node);
      }
    } else {
      warn!("Tried to touch a value that's not present ({:?})", elem);
    }
  }

  pub fn dequeue(&mut self) -> Option<T> {
    // get tail node
    let node = self.tail?;

    // unlink tail node
    unsafe {
      self.unlink_node(node);
    }

    // box node so it can be dropped
    let node_boxed = unsafe { Box::from_raw(node.as_ptr()) };
    // move element out of node
    let elem = node_boxed.elem;
    // get element hash
    let hash = unsafe { hash(&(*node.as_ptr()).elem) };
    // remove elem from index
    let _ = self.index.remove(&hash);

    Some(elem)
  }

  unsafe fn push_node(&mut self, node: NonNull<LRUNode<T>>) {
    // connect node to head
    (*node.as_ptr()).prev = None;
    (*node.as_ptr()).next = self.head;

    // connect list to node
    match self.head {
      None => self.tail = Some(node),
      Some(head) => (*head.as_ptr()).prev = Some(node),
    }

    self.head = Some(node);
  }

  unsafe fn unlink_node(&mut self, node: NonNull<LRUNode<T>>) {
    match (*node.as_ptr()).prev {
      Some(prev) => (*prev.as_ptr()).next = (*node.as_ptr()).next,
      None => self.head = (*node.as_ptr()).next,
    }

    match (*node.as_ptr()).next {
      Some(next) => (*next.as_ptr()).prev = (*node.as_ptr()).prev,
      None => self.tail = (*node.as_ptr()).prev,
    }

    (*node.as_ptr()).next = None;
    (*node.as_ptr()).prev = None;
  }
}

impl<T: Debug + Hash> Drop for LRU<T> {
  fn drop(&mut self) {
    while let Some(node) = self.head {
      let node = unsafe { Box::from_raw(node.as_ptr()) };
      self.head = node.next;
    }
  }
}

#[inline]
fn hash<T: Hash>(t: &T) -> u64 {
  let mut hasher = DefaultHasher::new();
  t.hash(&mut hasher);
  hasher.finish()
}

pub enum Or<A, B> {
  A(A),
  B(B),
}

impl<A, B> Or<A, B> {
  pub fn is_a(&self) -> bool {
    match self {
      Self::A(_) => true,
      Self::B(_) => false,
    }
  }

  pub fn is_b(&self) -> bool {
    !self.is_a()
  }

  pub fn a(&self) -> Option<&A> {
    match self {
      Self::A(ref a) => Some(a),
      Self::B(_) => None,
    }
  }

  pub fn b(&self) -> Option<&B> {
    match self {
      Self::A(_) => None,
      Self::B(ref b) => Some(b),
    }
  }

  pub fn a_mut(&mut self) -> Option<&mut A> {
    match self {
      Self::A(ref mut a) => Some(a),
      Self::B(_) => None,
    }
  }

  pub fn b_mut(&mut self) -> Option<&mut B> {
    match self {
      Self::A(_) => None,
      Self::B(ref mut b) => Some(b),
    }
  }

  pub fn extract_a(self) -> Option<A> {
    match self {
      Self::A(a) => Some(a),
      Self::B(_) => None,
    }
  }

  pub fn extract_b(self) -> Option<B> {
    match self {
      Self::A(_) => None,
      Self::B(b) => Some(b),
    }
  }

  pub fn unwrap_a(self) -> A {
    match self {
      Self::A(a) => a,
      Self::B(_) => panic!("Tried to unwrap_a from a B value"),
    }
  }

  pub fn unwrap_b(self) -> B {
    match self {
      Self::A(_) => panic!("Tried to unwrap_b from an A value"),
      Self::B(b) => b,
    }
  }

  pub fn expect_a<S: AsRef<str>>(self, msg: S) -> A {
    match self {
      Self::A(a) => a,
      Self::B(_) => panic!("{}", msg.as_ref()),
    }
  }

  pub fn expect_b<S: AsRef<str>>(self, msg: S) -> B {
    match self {
      Self::A(_) => panic!("{}", msg.as_ref()),
      Self::B(b) => b,
    }
  }

  pub fn fuse<F, G, O>(&self, f: F, g: G) -> O
  where
    F: FnOnce(&A) -> O,
    G: FnOnce(&B) -> O,
  {
    match self {
      Self::A(ref a) => f(a),
      Self::B(ref b) => g(b),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

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
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 1);
    assert_eq!(queue.dequeue(), Some(3));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.enqueue(2);
    queue.enqueue(3);
    queue.touch(&2);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.dequeue(), Some(3));
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.touch(&1);
    assert_eq!(queue.len(), 1);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.len(), 0);

    queue.enqueue(1);
    queue.enqueue(2);
    queue.touch(&1);
    queue.touch(&2);
    assert_eq!(queue.len(), 2);
    assert_eq!(queue.dequeue(), Some(1));
    assert_eq!(queue.dequeue(), Some(2));
    assert_eq!(queue.len(), 0);
  }
}
