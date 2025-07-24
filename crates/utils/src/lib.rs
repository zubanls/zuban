pub mod panic_context;

use std::{borrow::Cow, cell::UnsafeCell, fmt, path::PathBuf, pin::Pin};

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

    pub fn is_empty(&self) -> bool {
        unsafe { &*self.vec.get() }.is_empty()
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

    /// # Safety
    ///
    /// This function should only be called if you NEVER push elements while iterating its items.
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

    pub fn into_iter(self) -> impl Iterator<Item = Pin<Box<T>>> {
        self.vec.into_inner().into_iter()
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
