use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::pin::Pin;
use std::hash::{Hash, Hasher};
use std::fmt;

use parsa_python::PythonNode;
use parsa::{Node, NodeIndex};


#[macro_export]
macro_rules! debug {
    ($($arg:tt)*) => {
        if cfg!(feature="zuban_debug") {
            println!($($arg)*);
        }
    }
}

#[derive(Debug)]
pub struct InsertOnlyVec<T: ?Sized> {
    vec: UnsafeCell<Vec<Pin<Box<T>>>>,
}

impl<T: ?Sized> Default for InsertOnlyVec<T> {
    fn default() -> Self {
        Self {vec: UnsafeCell::new(vec![])}
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

    pub fn last(&self) -> Option<&T> {
        unsafe {&*self.vec.get()}.last().map(|x| x as &T)
    }
}

pub struct InsertOnlyHashMap<K, V> {
    map: UnsafeCell<HashMap<K, V>>,
}

impl<K, V: fmt::Debug> InsertOnlyHashMap<K, V> {
    pub fn len(&self) -> usize {
        unsafe {&*self.map.get()}.len()
    }
}

impl<K: Eq + Hash, V: fmt::Debug+Clone> InsertOnlyHashMap<K, V> {
    // unsafe, because the vec might be changed during its use.
    pub fn get(&self, key: &K) -> Option<V> {
        unsafe {&*self.map.get()}.get(key).cloned()
    }

    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let map = unsafe {&mut *self.map.get()};
        map.insert(key, value)
    }
}

impl<K, V> Default for InsertOnlyHashMap<K, V> {
    fn default() -> Self {
        Self {map: UnsafeCell::new(HashMap::new())}
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for InsertOnlyHashMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe {&*self.map.get()}.fmt(f)
    }
}

pub struct HashableRawStr {
    ptr: *const str
}

impl HashableRawStr {
    pub fn new(string: &str) -> Self {
        Self {ptr: string}
    }

    fn get_str(&self) -> &str {
        // This is REALLY unsafe. The user of HashableRawStr is responsible for
        // ensuring that the code part lives longer than this piece.
        unsafe {&*self.ptr}
    }
}

impl Hash for HashableRawStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_str().hash(state);
    }
}


impl PartialEq for HashableRawStr {
    fn eq(&self, other: &Self) -> bool {
        self.get_str() == other.get_str()
    }
}

impl Eq for HashableRawStr {}

impl fmt::Debug for HashableRawStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.get_str())
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
    pub fn add_symbol(&self, name: PythonNode) {
        debug_assert!(
            self.symbols.insert(HashableRawStr::new(name.get_code()), name.index as u32).is_none()
        );
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeIndex> {
        self.symbols.get(&HashableRawStr::new(name))
    }
}
