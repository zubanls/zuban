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

#[derive(Debug)]
pub struct InsertOnlyHashMapVec<K, T> {
    map: UnsafeCell<HashMap<K, Vec<T>>>,
}

impl<K, T: std::fmt::Debug> InsertOnlyHashMapVec<K, T> {
    pub fn len(&self) -> usize {
        unsafe {&*self.map.get()}.len()
    }
}

impl<K: Eq + std::hash::Hash, T: std::fmt::Debug> InsertOnlyHashMapVec<K, T> {
    // unsafe, because the vec might be changed during its use.
    unsafe fn get_iterator<'a, 'b>(&'a self, key: &'b K) -> std::option::Iter<&'a Vec<T>> {
        unsafe {&*self.map.get()}.get(key).iter()
    }

    pub fn push_to_vec(&self, key: K, value: T) {
        let map = unsafe {&mut *self.map.get()};
        match map.get_mut(&key) {
            Some(entry) => entry.push(value),
            None => {map.insert(key, vec![value]);},
        };
    }
}

impl<K, T> Default for InsertOnlyHashMapVec<K, T> {
    fn default() -> Self {
        Self {map: UnsafeCell::new(HashMap::new())}
    }
}
