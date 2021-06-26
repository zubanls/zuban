use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::pin::Pin;
use std::hash::{Hash, Hasher};
use std::fmt;

use crate::file::ValuesOrReferences;
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

    pub fn last(&self) -> Option<&T> {
        unsafe {&*self.vec.get()}.last().map(|x| x as &T)
    }
}

pub struct InsertOnlyHashMapVec<K, T> {
    map: UnsafeCell<HashMap<K, Vec<T>>>,
}

impl<K, T: fmt::Debug> InsertOnlyHashMapVec<K, T> {
    pub fn len(&self) -> usize {
        unsafe {&*self.map.get()}.len()
    }
}

impl<K: Eq + Hash, T: fmt::Debug> InsertOnlyHashMapVec<K, T> {
    // unsafe, because the vec might be changed during its use.
    pub unsafe fn get_iterator<'a, 'b>(&'a self, key: &'b K) -> std::slice::Iter<T> {
        match {&*self.map.get()}.get(key) {
            Some(v) => v.iter(),
            None => [].iter(),
        }
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

impl<K: fmt::Debug, T: fmt::Debug> fmt::Debug for InsertOnlyHashMapVec<K, T> {
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
pub struct DefinitionNames {
    definitions: InsertOnlyHashMapVec<HashableRawStr, NodeIndex>,
}

impl DefinitionNames {
    pub fn add_definition(&self, name: PythonNode) {
        self.definitions.push_to_vec(HashableRawStr::new(name.get_code()), name.index as u32);
    }

    pub fn lookup_global_definition(
        &self, values_or_references: &ValuesOrReferences, name: &str
    ) -> Option<NodeIndex> {
        self.reversed(name)
            .filter(|&n| values_or_references[*n as usize].get().in_module_scope())
            .next()
            .cloned()
    }

    pub fn lookup_definition(&self, name: &str) -> Option<NodeIndex> {
        self.reversed(name).next().cloned()
    }

    fn reversed(&self, name: &str) -> std::iter::Rev<std::slice::Iter<NodeIndex>> {
        unsafe {self.definitions.get_iterator(&HashableRawStr::new(name))}.rev()
    }
}
