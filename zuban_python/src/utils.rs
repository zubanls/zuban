use std::{
    borrow::Cow,
    cell::{Cell, Ref, UnsafeCell},
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    pin::Pin,
    rc::Rc,
};

use parsa_python_cst::{Name, NodeIndex};

thread_local!(pub static DEBUG_INDENTATION: Cell<usize> = const { Cell::new(0) });

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

#[macro_export]
macro_rules! new_class {
    ($link:expr, $($arg:expr),+$(,)?) => {
        $crate::type_::Type::new_class(
            $link,
            $crate::type_::ClassGenerics::List($crate::type_::GenericsList::new_generics(Rc::new([
                $($crate::type_::GenericItem::TypeArg($arg)),*
            ])))
        )
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

#[derive(Clone)]
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

#[derive(Debug, Default, Clone)]
pub struct SymbolTable {
    // The name symbol table comes from compiler theory, it's basically a mapping of a name to a
    // pointer. To avoid wasting space, we don't use a pointer here, instead we use the node index,
    // which acts as one.
    symbols: HashMap<HashableRawStr, NodeIndex>,
}

impl SymbolTable {
    pub fn iter(&self) -> impl Iterator<Item = (&str, &NodeIndex)> {
        // This should only ever be called on a table that is not still mutated.
        self.symbols.iter().map(|(k, v)| (k.as_str(), v))
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn add_or_replace_symbol(&mut self, name: Name) -> Option<NodeIndex> {
        self.symbols
            .insert(HashableRawStr::new(name.as_str()), name.index())
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeIndex> {
        self.symbols.get(&HashableRawStr::new(name)).copied()
    }
}

pub struct VecRefWrapper<'a, T: 'a>(pub Ref<'a, Vec<T>>);

impl<'a, 'b: 'a, T: 'a> IntoIterator for &'b VecRefWrapper<'a, T> {
    type IntoIter = std::slice::Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> std::slice::Iter<'a, T> {
        self.0.iter()
    }
}

pub fn bytes_repr(bytes: Cow<[u8]>) -> String {
    let mut string = String::new();
    for b in bytes.iter() {
        if b.is_ascii_graphic() {
            string.push(*b as char);
        } else {
            string += &format!("\\x{:#02x}", b);
        }
    }
    format!("b'{string}'")
}

pub fn str_repr(content: &str) -> String {
    let mut repr = String::new();
    for c in content.chars() {
        if c.is_ascii_control() {
            match c {
                '\n' => repr += "\\n",
                '\r' => repr += "\\r",
                '\t' => repr += "\\t",
                _ => {
                    repr += "\\";
                    repr += &format!("{:#04x}", c as u8)[1..];
                }
            }
        } else if c == '\\' {
            repr += r"\\";
        } else {
            repr.push(c);
        }
    }
    format!("'{repr}'")
}

// Tracking Issue for arc_unwrap_or_clone is unstable, see https://github.com/rust-lang/rust/issues/93610
pub fn rc_unwrap_or_clone<T: Clone>(this: Rc<T>) -> T {
    Rc::try_unwrap(this).unwrap_or_else(|arc| (*arc).clone())
}

pub fn join_with_commas(input: impl Iterator<Item = String>) -> String {
    input.collect::<Vec<_>>().join(", ")
}

pub fn rc_slice_into_vec<T: Clone>(this: Rc<[T]>) -> Vec<T> {
    // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612

    // TODO we could avoid cloning here and just use a copy for the slice parts.
    // See also some discussion how this could be done here:
    // https://stackoverflow.com/questions/77511698/rct-try-unwrap-into-vect#comment136989622_77511997
    Vec::from(this.as_ref())
}
