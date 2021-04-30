use std::cell::UnsafeCell;
use std::pin::Pin;

#[derive(Debug)]
pub struct InsertOnlyVec<T: ?Sized> {
    vec: UnsafeCell<Vec<Pin<Box<T>>>>,
}

impl<T: ?Sized> Default for InsertOnlyVec<T> {
    fn default() -> Self {
        Self {vec: UnsafeCell::new(vec!())}
    }
}

impl<T: ?Sized> InsertOnlyVec<T> where Pin<Box<T>>: Sized {
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

