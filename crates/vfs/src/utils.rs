use std::ops::{Deref, DerefMut};
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

pub struct VecRwLockWrapper<'a, U, T: 'a>(pub(crate) MappedReadGuard<'a, U, Vec<T>>);

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
