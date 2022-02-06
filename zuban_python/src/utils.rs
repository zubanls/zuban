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
    pub fn add_or_replace_symbol(&self, name: Name) -> Option<NodeIndex> {
        self.symbols
            .insert(HashableRawStr::new(name.as_str()), name.index())
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeIndex> {
        self.symbols.get(&HashableRawStr::new(name))
    }
}
