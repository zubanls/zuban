use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::pin::Pin;
use std::iter::Cloned;
use parsa::NodeIndex;

#[derive(Debug)]
pub struct InsertOnlyVec<T: ?Sized> {
    vec: UnsafeCell<Vec<Pin<Box<T>>>>,
}

impl<T: ?Sized> Default for InsertOnlyVec<T> {
    fn default() -> Self {
        Self {vec: UnsafeCell::new(vec!())}
    }
}

impl<T: ?Sized> InsertOnlyVec<T> {
    pub fn get(&self, index: usize) -> Option<&T> {
        unsafe {&*self.vec.get()}.get(index).map(|x| x as &T)
    }

    pub fn push(&self, element: Pin<Box<T>>) {
        unsafe {&mut *self.vec.get()}.push(element);
    }

    pub fn len(&self) -> usize {
        unsafe {&*self.vec.get()}.len()
    }
}

#[derive(Debug, Default)]
pub struct InsertOnlyHashMapVec<K, T> {
    map: HashMap<K, Vec<T>>,
}

impl<K, T: std::fmt::Debug> InsertOnlyHashMapVec<K, T> {
    pub fn len(&self) -> usize {
        self.map.len()
    }
}

impl<K: Eq + std::hash::Hash, T: std::fmt::Debug> InsertOnlyHashMapVec<K, T> {
    // unsafe, because the vec might be changed during its use.
    unsafe fn get_iterator<'a, 'b>(&'a self, key: &'b K) -> std::slice::Iter<T> {
        match self.map.get(key) {
            Some(v) => v.iter(),
            None => [].iter(),
        }
    }

    pub fn push_to_vec(&self, key: K, value: T) {
        let mut_self = unsafe {&mut *(self as *const Self as *mut Self)};
        match mut_self.map.get_mut(&key) {
            Some(entry) => entry.push(value),
            None => {mut_self.map.insert(key, vec![value]);},
        };
    }
}
