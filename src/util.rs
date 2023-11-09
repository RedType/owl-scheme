use std::{
  cell::RefCell,
  collections::HashMap,
  fmt::Debug,
  hash::Hash,
  rc::{Rc, Weak},
};
use log::*;

#[derive(Debug)]
pub struct LRU<T: Debug + Eq + Hash> {
  index: HashMap<T, Rc<RefCell<LRUNode<T>>>>,
  head: Option<Rc<RefCell<LRUNode<T>>>>,
  tail: Option<Rc<RefCell<LRUNode<T>>>>,
}

#[derive(Debug)]
struct LRUNode<T: Debug + Eq + Hash> {
  elem: T,
  prev: Option<Weak<RefCell<LRUNode<T>>>>,
  next: Option<Rc<RefCell<LRUNode<T>>>>,
}

impl<T: Debug + Eq + Hash> LRU<T> {
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

  pub fn enqueue(&mut self, elem: T) {
    if self.index.contains_key(&elem) {
      warn!("Attempted to enqueue already-existing cache element {:?}", elem);
      self.touch(elem);
      return;
    }

    let mut new_head = Rc::new(RefCell::new(LRUNode {
      elem,
      prev: None,
      next: self.head.as_ref().map(|h| Rc::clone(h)),
    }));

    if let Some(h) = self.head {
      h.borrow_mut().prev = Some(Rc::downgrade(&new_head));
    } else {
      self.tail = Some(Rc::clone(&new_head));
    }

    self.head = Some(Rc::clone(&new_head));

    self.index.insert(elem, new_head);
  }

  pub fn dequeue(&mut self) -> Option<T> {
    if let Some(tail) = self.tail {
      if let Some(prev) = tail.borrow_mut().prev.as_ref().map(|p| Weak::upgrade(p).unwrap()) {
        prev.borrow_mut().next = None;
        self.tail = Some(prev);
      } else { // tail is our last element
        self.head = None;
        self.tail = None;
      }
      self.index.remove(&tail.borrow().elem);
      Some(tail.borrow().elem)
    } else { // list is empty
      None
    }
  }

  pub fn touch(&mut self, elem: T)  {
    if let Some(node) = self.index.get(&elem).as_ref().map(|node| Rc::clone(node)) {
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
      warn!("Attempted to touch {:?}, which was not in the LRU cache", elem);
      self.enqueue(elem);
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

