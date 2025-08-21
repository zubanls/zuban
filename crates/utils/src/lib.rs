pub mod panic_context;

use std::{
    borrow::Cow,
    cell::UnsafeCell,
    fmt,
    ops::{Deref, DerefMut},
    path::PathBuf,
    pin::Pin,
    sync::{Mutex, RwLockReadGuard, RwLockWriteGuard},
};

use fnv::{FnvHashMap, FnvHashSet};

pub type FastHashMap<K, V> = FnvHashMap<K, V>;
pub type FastHashSet<T> = FnvHashSet<T>;

pub fn config_dir_path() -> Option<PathBuf> {
    dirs::config_dir().map(|p| p.join("zuban"))
}

pub struct InsertOnlyVec<T: ?Sized> {
    vec: Mutex<UnsafeCell<Vec<Pin<Box<T>>>>>,
}

impl<T: ?Sized> From<Vec<Pin<Box<T>>>> for InsertOnlyVec<T> {
    fn from(value: Vec<Pin<Box<T>>>) -> Self {
        Self {
            vec: Mutex::new(UnsafeCell::new(value)),
        }
    }
}

impl<T: ?Sized> Default for InsertOnlyVec<T> {
    fn default() -> Self {
        Self {
            vec: Mutex::new(UnsafeCell::new(vec![])),
        }
    }
}

impl<T: ?Sized + Unpin> InsertOnlyVec<T> {
    pub fn get(&self, index: usize) -> Option<&T> {
        unsafe { &*self.vec.lock().unwrap().get() }
            .get(index)
            .map(|x| x as &T)
    }

    /*
     * TODO remove this?
    pub fn get_mut(&mut self, index: usize) -> Option<Pin<&mut T>> {
        self.vec.get_mut().get_mut(index).map(|x| x.as_mut())
    }
    */

    pub fn push(&self, element: Pin<Box<T>>) -> (&T, usize) {
        let guard = self.vec.lock().unwrap();
        let vec = unsafe { &mut *guard.get() };
        vec.push(element);
        (vec.last().unwrap(), vec.len() - 1)
    }

    pub fn len(&self) -> usize {
        unsafe { &*self.vec.lock().unwrap().get() }.len()
    }

    pub fn is_empty(&self) -> bool {
        unsafe { &*self.vec.lock().unwrap().get() }.is_empty()
    }

    pub fn last(&self) -> Option<&T> {
        unsafe { &*self.vec.lock().unwrap().get() }
            .last()
            .map(|x| x as &T)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.vec
            .get_mut()
            .unwrap()
            .get_mut()
            .iter_mut()
            .map(|x| x as &mut T)
    }

    pub fn clear(&mut self) {
        self.vec.get_mut().unwrap().get_mut().clear()
    }

    /// # Safety
    ///
    /// This function should only be called if you NEVER push elements while iterating its items.
    pub unsafe fn iter(&self) -> impl Iterator<Item = &T> {
        // Because the size of the vec can grow and shrink at any point, this is an unsafe
        // operation.
        (*self.vec.lock().unwrap().get()).iter().map(|x| x as &T)
    }

    pub fn set(&mut self, index: usize, obj: Pin<Box<T>>) {
        self.vec.get_mut().unwrap().get_mut()[index] = obj;
    }

    pub fn as_vec_mut(&mut self) -> &mut Vec<Pin<Box<T>>> {
        self.vec.get_mut().unwrap().get_mut()
    }

    pub fn into_iter(self) -> impl Iterator<Item = Pin<Box<T>>> {
        self.vec.into_inner().unwrap().into_inner().into_iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for InsertOnlyVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { &*self.vec.lock().unwrap().get() }.fmt(f)
    }
}

impl<T: ?Sized> std::ops::Index<usize> for InsertOnlyVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        unsafe { &*self.vec.lock().unwrap().get() }.index(index)
    }
}

impl<T: ?Sized + Unpin> std::ops::IndexMut<usize> for InsertOnlyVec<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.vec.get_mut().unwrap().get_mut()[index]
    }
}
impl<T: ?Sized> Clone for InsertOnlyVec<T>
where
    Box<T>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            vec: Mutex::new(UnsafeCell::new(
                unsafe { &*self.vec.lock().unwrap().get() }.clone(),
            )),
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

pub struct AlreadySeen<'a, T> {
    pub current: T,
    pub previous: Option<&'a AlreadySeen<'a, T>>,
}

impl<T: PartialEq<T>> AlreadySeen<'_, T> {
    pub fn is_cycle(&self) -> bool {
        self.iter_ancestors()
            .any(|ancestor| *ancestor == self.current)
    }
}

impl<'a, T> AlreadySeen<'a, T> {
    pub fn new(current: T) -> Self {
        Self {
            current,
            previous: None,
        }
    }

    pub fn iter_ancestors(&self) -> AlreadySeenIterator<'a, T> {
        AlreadySeenIterator(self.previous)
    }

    pub fn append<'x: 'a>(&'x self, current: T) -> AlreadySeen<'x, T> {
        Self {
            current,
            previous: Some(self),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for AlreadySeen<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter_ancestors()).finish()
    }
}

impl<T: Clone> Clone for AlreadySeen<'_, T> {
    fn clone(&self) -> Self {
        Self {
            current: self.current.clone(),
            previous: self.previous,
        }
    }
}

impl<T: Copy> Copy for AlreadySeen<'_, T> {}

pub struct AlreadySeenIterator<'a, T>(Option<&'a AlreadySeen<'a, T>>);

impl<'a, T> Iterator for AlreadySeenIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let first = self.0.take()?;
        let result = Some(&first.current);
        self.0 = first.previous;
        result
    }
}

pub fn dedent(s: &str) -> String {
    dedent_cow(Cow::Borrowed(s)).into_owned()
}

pub fn dedent_cow(s: Cow<str>) -> Cow<str> {
    let mut indent = usize::MAX;
    let lines: &Vec<_> = &s.split('\n').collect();
    for line in lines {
        if !line.trim().is_empty() {
            indent = std::cmp::min(indent, line.len() - line.trim_start().len());
        }
    }
    if indent == usize::MAX {
        return s;
    }
    let new_lines: Vec<_> = lines
        .iter()
        .map(|line| {
            if line.len() >= indent {
                &line[indent..]
            } else {
                line
            }
        })
        .collect();
    Cow::Owned(new_lines.join("\n"))
}

pub struct VecRwLockWrapper<'a, U, T: 'a>(pub(crate) MappedReadGuard<'a, U, Vec<T>>);

impl<'a, U, T: 'a> VecRwLockWrapper<'a, U, T> {
    pub fn new(mapped: MappedReadGuard<'a, U, Vec<T>>) -> Self {
        Self(mapped)
    }
}

impl<'a, 'b: 'a, U, T: 'a> IntoIterator for &'b VecRwLockWrapper<'a, U, T> {
    type IntoIter = std::slice::Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.0.iter()
    }
}

// TODO we want mapped_lock_guards from https://github.com/rust-lang/rust/issues/117108
// this is just an ugly workaround and I'm not even sure it is safe.
/// A "mapped" read guard, holding the original guard
/// and a pointer to the projected field.
pub struct MappedReadGuard<'a, T: ?Sized, U: ?Sized> {
    _guard: RwLockReadGuard<'a, T>,
    value: *const U,
}

impl<'a, T: ?Sized, U: ?Sized> MappedReadGuard<'a, T, U> {
    pub fn map(_guard: RwLockReadGuard<'a, T>, f: impl FnOnce(&T) -> &U) -> Self {
        let value = f(&*_guard) as *const U;
        Self { _guard, value }
    }
}

impl<'a, T: ?Sized, U: ?Sized> Deref for MappedReadGuard<'a, T, U> {
    type Target = U;
    fn deref(&self) -> &U {
        // Safety: `value` comes from `&*guard` and guard outlives this
        unsafe { &*self.value }
    }
}

impl<'a, T, U: std::fmt::Debug> std::fmt::Debug for MappedReadGuard<'a, T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MappedReadGuard")
            .field("value", self.deref())
            .finish()
    }
}

// TODO we want mapped_lock_guards from https://github.com/rust-lang/rust/issues/117108
// this is just an ugly workaround and I'm not even sure it is safe.
pub struct MappedWriteGuard<'a, T: ?Sized, U: ?Sized> {
    _guard: RwLockWriteGuard<'a, T>,
    value: *mut U,
}

impl<'a, T: ?Sized, U: ?Sized> MappedWriteGuard<'a, T, U> {
    pub fn map(mut _guard: RwLockWriteGuard<'a, T>, f: impl FnOnce(&mut T) -> &mut U) -> Self {
        let value = f(&mut *_guard) as *mut U;
        Self { _guard, value }
    }
}

impl<'a, T: ?Sized, U: ?Sized> Deref for MappedWriteGuard<'a, T, U> {
    type Target = U;
    fn deref(&self) -> &U {
        // Safety: `value` comes from `&*guard` and guard outlives this
        unsafe { &*self.value }
    }
}
impl<'a, T: ?Sized, U: ?Sized> DerefMut for MappedWriteGuard<'a, T, U> {
    fn deref_mut(&mut self) -> &mut U {
        // Safety: `value` comes from `&*guard` and guard outlives this
        unsafe { &mut *self.value }
    }
}
