use std::{cell::UnsafeCell, fmt, path::PathBuf, pin::Pin};

use fnv::{FnvHashMap, FnvHashSet};

pub type FastHashMap<K, V> = FnvHashMap<K, V>;
pub type FastHashSet<T> = FnvHashSet<T>;

pub fn config_dir_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("zuban"))
}

pub struct InsertOnlyVec<T: ?Sized> {
    vec: UnsafeCell<Vec<Pin<Box<T>>>>,
}

impl<T: ?Sized> From<Vec<Pin<Box<T>>>> for InsertOnlyVec<T> {
    fn from(value: Vec<Pin<Box<T>>>) -> Self {
        Self {
            vec: UnsafeCell::new(value),
        }
    }
}

impl<T: ?Sized> Default for InsertOnlyVec<T> {
    fn default() -> Self {
        Self {
            vec: UnsafeCell::new(vec![]),
        }
    }
}

impl<T: ?Sized + Unpin> InsertOnlyVec<T> {
    pub fn get(&self, index: usize) -> Option<&T> {
        unsafe { &*self.vec.get() }.get(index).map(|x| x as &T)
    }

    /*
     * TODO remove this?
    pub fn get_mut(&mut self, index: usize) -> Option<Pin<&mut T>> {
        self.vec.get_mut().get_mut(index).map(|x| x.as_mut())
    }
    */

    pub fn push(&self, element: Pin<Box<T>>) {
        unsafe { &mut *self.vec.get() }.push(element);
    }

    pub fn len(&self) -> usize {
        unsafe { &*self.vec.get() }.len()
    }

    pub fn last(&self) -> Option<&T> {
        unsafe { &*self.vec.get() }.last().map(|x| x as &T)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.vec.get_mut().iter_mut().map(|x| x as &mut T)
    }

    pub fn clear(&mut self) {
        self.vec.get_mut().clear()
    }

    pub unsafe fn iter(&self) -> impl Iterator<Item = &T> {
        // Because the size of the vec can grow and shrink at any point, this is an unsafe
        // operation.
        (*self.vec.get()).iter().map(|x| x as &T)
    }

    pub fn set(&mut self, index: usize, obj: Pin<Box<T>>) {
        self.vec.get_mut()[index] = obj;
    }

    pub fn as_vec_mut(&mut self) -> &mut Vec<Pin<Box<T>>> {
        self.vec.get_mut()
    }
}

impl<T: fmt::Debug> fmt::Debug for InsertOnlyVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { &*self.vec.get() }.fmt(f)
    }
}

impl<T: ?Sized> std::ops::Index<usize> for InsertOnlyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        unsafe { &*self.vec.get() }.index(index)
    }
}

impl<T: ?Sized + Unpin> std::ops::IndexMut<usize> for InsertOnlyVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.vec.get_mut()[index]
    }
}
impl<T: ?Sized> Clone for InsertOnlyVec<T>
where
    Box<T>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            vec: UnsafeCell::new(unsafe { &*self.vec.get() }.clone()),
        }
    }
}

pub fn match_case(case_sensitive: bool, x: &str, y: &str) -> bool {
    if case_sensitive {
        x == y
    } else {
        x.eq_ignore_ascii_case(y)
    }
}
