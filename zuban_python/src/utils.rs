use std::cell::{Cell, UnsafeCell};
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::pin::Pin;

use parsa_python_ast::{Name, NodeIndex};

use crate::database::FileIndex;

thread_local!(pub static DEBUG_INDENTATION: Cell<usize> = Cell::new(0));

#[inline]
pub fn debug_indent<C: FnOnce() -> T, T>(f: C) -> T {
    if cfg!(feature = "zuban_debug") {
        DEBUG_INDENTATION.with(|i| {
            i.set(i.get() + 1);
            let result = f();
            i.set(i.get() - 1);
            result
        })
    } else {
        f()
    }
}

#[macro_export]
macro_rules! debug {
    ($($arg:tt)*) => {
        if cfg!(feature="zuban_debug") {
            use std::iter::repeat;
            let indent = $crate::utils::DEBUG_INDENTATION.with(|i| i.get());
            print!("{}", repeat(' ').take(indent).collect::<String>());
            println!($($arg)*);
        }
    }
}

pub struct InsertOnlyVec<T: ?Sized> {
    vec: UnsafeCell<Vec<Pin<Box<T>>>>,
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

    pub fn get_mut(&mut self, index: usize) -> Option<Pin<&mut T>> {
        self.vec.get_mut().get_mut(index).map(|x| x.as_mut())
    }

    pub fn push(&self, element: Pin<Box<T>>) {
        unsafe { &mut *self.vec.get() }.push(element);
    }

    pub fn len(&self) -> usize {
        unsafe { &*self.vec.get() }.len()
    }

    pub fn last(&self) -> Option<&T> {
        unsafe { &*self.vec.get() }.last().map(|x| x as &T)
    }

    pub unsafe fn iter(&self) -> impl Iterator<Item = &T> {
        // Because the size of the vec can grow and shrink at any point, this is an unsafe
        // operation.
        (&*self.vec.get()).iter().map(|x| x as &T)
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

impl<K, V: fmt::Debug> InsertOnlyHashMap<K, V> {
    pub fn len(&self) -> usize {
        unsafe { &*self.map.get() }.len()
    }
}

impl<K: Eq + Hash, V: fmt::Debug + Clone> InsertOnlyHashMap<K, V> {
    // unsafe, because the vec might be changed during its use.
    pub fn get(&self, key: &K) -> Option<V> {
        unsafe { &*self.map.get() }.get(key).cloned()
    }

    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let map = unsafe { &mut *self.map.get() };
        map.insert(key, value)
    }

    unsafe fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        let map = &mut *self.map.get();
        map.iter()
    }
}

impl<K, V> Default for InsertOnlyHashMap<K, V> {
    fn default() -> Self {
        Self {
            map: UnsafeCell::new(HashMap::new()),
        }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for InsertOnlyHashMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { &*self.map.get() }.fmt(f)
    }
}

pub struct Invalidations {
    vec: UnsafeCell<Vec<FileIndex>>,
}

impl Default for Invalidations {
    fn default() -> Self {
        Self {
            vec: UnsafeCell::new(vec![]),
        }
    }
}

impl std::clone::Clone for Invalidations {
    fn clone(&self) -> Self {
        Self {
            vec: UnsafeCell::new(unsafe { &*self.vec.get() }.clone()),
        }
    }
}

impl Invalidations {
    pub fn add(&self, element: FileIndex) {
        let vec = unsafe { &mut *self.vec.get() };
        if !vec.contains(&element) {
            vec.push(element);
        }
    }

    pub fn into_iter(self) -> impl Iterator<Item = FileIndex> {
        self.vec.into_inner().into_iter()
    }

    pub fn get_mut(&mut self) -> &mut Vec<FileIndex> {
        self.vec.get_mut()
    }
}

impl fmt::Debug for Invalidations {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { &*self.vec.get() }.fmt(f)
    }
}

pub struct InsertOnlyHashMap<K, V> {
    map: UnsafeCell<HashMap<K, V>>,
}

pub struct HashableRawStr {
    ptr: *const str,
}

impl HashableRawStr {
    pub fn new(string: &str) -> Self {
        Self { ptr: string }
    }

    fn as_str(&self) -> &str {
        // This is REALLY unsafe. The user of HashableRawStr is responsible for
        // ensuring that the code part lives longer than this piece.
        unsafe { &*self.ptr }
    }
}

impl Hash for HashableRawStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl PartialEq for HashableRawStr {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for HashableRawStr {}

impl fmt::Debug for HashableRawStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Debug, Default)]
pub struct SymbolTable {
    // The name symbol table comes from compiler theory, it's basically a mapping of a name to a
    // pointer. To avoid wasting space, we don't use a pointer here, instead we use the node index,
    // which acts as one.
    symbols: InsertOnlyHashMap<HashableRawStr, NodeIndex>,
}

impl SymbolTable {
    pub unsafe fn iter_on_finished_table(&self) -> impl Iterator<Item = (&str, &NodeIndex)> {
        // This should only ever be called on a table that is not still mutated.
        self.symbols.iter().map(|(k, v)| (k.as_str(), v))
    }

    pub fn add_or_replace_symbol(&self, name: Name) -> Option<NodeIndex> {
        self.symbols
            .insert(HashableRawStr::new(name.as_str()), name.index())
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeIndex> {
        self.symbols.get(&HashableRawStr::new(name))
    }
}

// SPECIAL: Copy of stdlib to be able to access the inner iter.
#[derive(Debug)]
pub struct Peekable<I: Iterator> {
    iter: I,
    /// Remember a peeked value, even if it was None.
    peeked: Option<Option<I::Item>>,
}

impl<I: Iterator> Peekable<I> {
    pub fn new(iter: I) -> Peekable<I> {
        Peekable { iter, peeked: None }
    }

    pub fn as_inner_mut(&mut self) -> &mut I {
        // Must never be Some(...), otherwise a value will be returned after changing the iterator.
        debug_assert!(self.peeked.is_none());
        &mut self.iter
    }
}

// Peekable must remember if a None has been seen in the `.peek()` method.
// It ensures that `.peek(); .peek();` or `.peek(); .next();` only advances the
// underlying iterator at most once. This does not by itself make the iterator
// fused.
impl<I: Iterator> Iterator for Peekable<I> {
    type Item = I::Item;

    #[inline]
    fn next(&mut self) -> Option<I::Item> {
        match self.peeked.take() {
            Some(v) => v,
            None => self.iter.next(),
        }
    }

    #[inline]
    fn count(self) -> usize {
        unreachable!()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<I::Item> {
        unreachable!()
    }

    #[inline]
    fn last(self) -> Option<I::Item> {
        unreachable!()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let peek_len = match self.peeked {
            Some(None) => return (0, Some(0)),
            Some(Some(_)) => 1,
            None => 0,
        };
        let (lo, hi) = self.iter.size_hint();
        let lo = lo.saturating_add(peek_len);
        let hi = match hi {
            Some(x) => x.checked_add(peek_len),
            None => None,
        };
        (lo, hi)
    }

    #[inline]
    fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R {
        unreachable!()
    }

    #[inline]
    fn fold<Acc, Fold>(self, init: Acc, fold: Fold) -> Acc {
        unreachable!()
    }
}

impl<I: Iterator> Peekable<I> {
    #[inline]
    pub fn peek(&mut self) -> Option<&I::Item> {
        let iter = &mut self.iter;
        self.peeked.get_or_insert_with(|| iter.next()).as_ref()
    }

    #[inline]
    pub fn peek_mut(&mut self) -> Option<&mut I::Item> {
        let iter = &mut self.iter;
        self.peeked.get_or_insert_with(|| iter.next()).as_mut()
    }

    pub fn next_if(&mut self, func: impl FnOnce(&I::Item) -> bool) -> Option<I::Item> {
        match self.next() {
            Some(matched) if func(&matched) => Some(matched),
            other => {
                // Since we called `self.next()`, we consumed `self.peeked`.
                assert!(self.peeked.is_none());
                self.peeked = Some(other);
                None
            }
        }
    }

    pub fn next_if_eq<T>(&mut self, expected: &T) -> Option<I::Item>
    where
        T: ?Sized,
        I::Item: PartialEq<T>,
    {
        self.next_if(|next| next == expected)
    }
}
