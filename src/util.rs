use std::{
  collections::HashMap,
  fmt::Debug,
  hash::{DefaultHasher, Hash, Hasher},
  marker::PhantomData,
  ptr::NonNull,
};
use log::*;

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
    let mut hasher = DefaultHasher::new();
    elem.hash(&mut hasher);
    let hash = hasher.finish();

    if self.index.contains_key(&hash) {
      warn!("Attempted to enqueue already-existing cache element {:?}", elem);
      self.touch(&elem);
      return;
    }

    let new_head = Box::new(LRUNode {
      elem,
      prev: None,
      next: self.head,
    });
    let new_head_ptr = NonNull::from(Box::leak(new_head));

    self.index.insert(hash, new_head_ptr);

    // push node to front
    unsafe {
      match self.head {
        None => self.tail = Some(new_head_ptr),
        Some(head) => (*head.as_ptr()).prev = Some(new_head_ptr),
      }
    }
    self.head = Some(new_head_ptr);
  }

  pub fn dequeue(&mut self) -> Option<T> {
    let tail = if let Some(tail) = self.tail {
        tail
    } else {
        return None;
    };

    // get hash
    let hash = unsafe {
      let mut hasher = DefaultHasher::new();
      (*tail.as_ptr()).elem.hash(&mut hasher);
      hasher.finish()
    };

    // remove element from the index
    self.index.remove(&hash);

    // remove back node from the list
    let elem = self.tail.map(|node| unsafe {
      let node = Box::from_raw(node.as_ptr());
      self.tail = node.prev;
      match self.tail {
        None => self.head = None,
        Some(tail) => (*tail.as_ptr()).next = None,
      }
      node.elem
    });

    elem
  }

  pub fn touch(&mut self, elem: &T) {
    let mut hasher = DefaultHasher::new();
    elem.hash(&mut hasher);
    let hash = hasher.finish();

    let node = if let Some(node) = self.index.get(&hash) {
        *node
    } else {
        return;
    };

    // cut node out of list
    unsafe {
      let prev = (*node.as_ptr()).prev;
      let next = (*node.as_ptr()).next;

      if let Some(prev) = prev {
        (*prev.as_ptr()).next = next;
      }

      if let Some(next) = next {
        (*next.as_ptr()).prev = prev;
      }
    }

    // push to front
    unsafe {
      match self.head {
        None => self.tail = Some(node),
        Some(head) => (*head.as_ptr()).prev = Some(node),
      }

      (*node.as_ptr()).next = self.head;
      self.head = Some(node);
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

