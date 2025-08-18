use std::{
    borrow::Cow,
    cell::Cell,
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    sync::Arc,
};

use parsa_python_cst::{Name, NodeIndex};

thread_local!(pub static DEBUG_INDENTATION: Cell<usize> = const { Cell::new(0) });

#[inline]
#[must_use]
pub fn debug_indent() -> DebugIndent {
    if cfg!(feature = "zuban_debug") {
        DEBUG_INDENTATION.with(|i| {
            i.set(i.get() + 1);
        })
    }
    DebugIndent()
}

pub struct DebugIndent();

impl Drop for DebugIndent {
    #[inline]
    fn drop(&mut self) {
        if cfg!(feature = "zuban_debug") {
            DEBUG_INDENTATION.with(|i| i.set(i.get() - 1));
        }
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
macro_rules! recoverable_error {
    ($($arg:tt)*) => {
        if std::env::var("ZUBAN_CRASH_ON_ERROR").is_ok_and(|s| s == "1") {
            panic!($($arg)*)
        } else {
            tracing::error!($($arg)*);
            tracing::error!("To crash on this error, use set the environment variable ZUBAN_CRASH_ON_ERROR=1");
        }
    }
}

#[macro_export]
macro_rules! new_class {
    ($link:expr, $($arg:expr),+$(,)?) => {
        $crate::type_::Type::new_class(
            $link,
            $crate::type_::ClassGenerics::List(
                $crate::type_::GenericsList::new_generics(std::sync::Arc::new([
                    $($crate::type_::GenericItem::TypeArg($arg)),*
                ]))
            )
        )
    }
}

#[derive(Clone)]
pub(crate) struct HashableRawStr {
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
pub(crate) struct SymbolTable {
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

    pub fn add_or_replace_symbol(&mut self, name: Name) -> Option<NodeIndex> {
        self.symbols
            .insert(HashableRawStr::new(name.as_str()), name.index())
    }

    pub fn lookup_symbol(&self, name: &str) -> Option<NodeIndex> {
        self.symbols.get(&HashableRawStr::new(name)).copied()
    }
}

pub fn bytes_repr(bytes: Cow<[u8]>) -> String {
    let mut string = String::with_capacity(bytes.len());
    for &b in bytes.iter() {
        match b {
            b'\t' => string.push_str(r"\t"),
            b'\n' => string.push_str(r"\n"),
            b'\r' => string.push_str(r"\r"),
            b'\\' => string.push_str(r"\\"),
            b' ' => string.push(' '),
            _ if b.is_ascii_graphic() => string.push(b as char),
            _ => string += &format!("\\x{:02x}", b),
        }
    }
    format!("b'{string}'")
}

pub fn str_repr(content: &str) -> String {
    let mut repr = String::new();
    for c in content.chars() {
        // Since the control characters cause an issue when printing to a terminal, we have to
        // escape this. Some of them also don't have a symbol that would show. Both C0 and C1 ansi
        // escape codes must be escaped.
        if c.is_control() {
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

pub fn join_with_commas(input: impl Iterator<Item = String>) -> String {
    input.collect::<Vec<_>>().join(", ")
}

pub fn arc_slice_into_vec<T: Clone>(this: Arc<[T]>) -> Vec<T> {
    // Performance issue: Rc -> Vec check https://github.com/rust-lang/rust/issues/93610#issuecomment-1528108612

    // TODO we could avoid cloning here and just use a copy for the slice parts.
    // See also some discussion how this could be done here:
    // https://stackoverflow.com/questions/77511698/rct-try-unwrap-into-vect#comment136989622_77511997
    Vec::from(this.as_ref())
}

#[inline]
pub fn is_magic_method(name: &str) -> bool {
    name.starts_with("__") && name.ends_with("__")
}

pub enum EitherIterator<IT1, IT2> {
    Left(IT1),
    Right(IT2),
}

impl<IT1, IT2, T> Iterator for EitherIterator<IT1, IT2>
where
    IT1: Iterator<Item = T>,
    IT2: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Left(iterator) => iterator.next(),
            Self::Right(iterator) => iterator.next(),
        }
    }
}
