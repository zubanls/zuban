use crate::database::{Database, FileIndex};
use crate::diagnostics::Diagnostic;
use crate::file::PythonFile;
use crate::inferred::Inferred;
use crate::name::{Name, Names, TreePosition};
use crate::utils::Invalidations;
use parsa_python_ast::{CodeIndex, Keyword, NodeIndex};
use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::fmt;
use std::fs;
use std::pin::Pin;

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = &'static dyn Fn(String) -> F;

pub trait Vfs {
    fn read_file(&self, path: &str) -> Option<String>;
}

#[derive(Default)]
pub struct FileSystemReader {}

impl Vfs for FileSystemReader {
    fn read_file(&self, path: &str) -> Option<String> {
        // TODO can error
        Some(fs::read_to_string(path).unwrap())
    }
}

#[derive(Debug)]
pub enum Leaf<'db> {
    Name(Box<dyn Name<'db> + 'db>),
    String,
    Number,
    Keyword(Keyword<'db>),
    None,
}

pub trait FileStateLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str>;

    fn might_be_relevant(&self, name: &str) -> bool;
    fn should_be_ignored(&self, name: &str) -> bool;

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState>>;

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState>>;
}

#[derive(Default)]
pub struct PythonFileLoader {}

impl FileStateLoader for PythonFileLoader {
    fn responsible_for_file_endings(&self) -> Vec<&str> {
        vec!["py", "pyi"]
    }

    fn might_be_relevant(&self, name: &str) -> bool {
        if name.ends_with(".py") {
            return true;
        }
        !name.contains('.') && !name.contains('-')
    }

    fn should_be_ignored(&self, name: &str) -> bool {
        name == "__pycache__" && !name.ends_with(".pyc")
    }

    fn load_parsed(&self, path: String, code: String) -> Pin<Box<dyn FileState>> {
        Box::pin(LanguageFileState::new_parsed(path, PythonFile::new(code)))
    }

    fn load_unparsed(&self, path: String) -> Pin<Box<dyn FileState>> {
        Box::pin(LanguageFileState::new_unparsed(path, &PythonFile::new))
    }
}

pub trait FileLoader<F> {
    fn load_file(&self, path: String, code: String) -> F;
}

pub trait AsAny {
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static;
}

impl<T> AsAny for T {
    fn as_any(&self) -> &dyn Any
    where
        Self: 'static,
    {
        self
    }
}

pub trait File: std::fmt::Debug + AsAny {
    fn implementation<'db>(&self, names: Names<'db>) -> Names<'db> {
        vec![]
    }
    fn leaf<'db>(&'db self, database: &'db Database, position: CodeIndex) -> Leaf<'db>;
    fn infer_operator_leaf<'db>(
        &'db self,
        database: &'db Database,
        keyword: Keyword<'db>,
    ) -> Inferred<'db>;
    fn file_index(&self) -> FileIndex;
    fn set_file_index(&self, index: FileIndex);

    fn node_start_position(&self, n: NodeIndex) -> TreePosition;
    fn node_end_position(&self, n: NodeIndex) -> TreePosition;
    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex;
    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize);

    fn file_path<'db>(&self, database: &'db Database) -> &'db str {
        database.file_path(self.file_index())
    }

    fn diagnostics<'db>(&'db self, db: &'db Database) -> Box<[Diagnostic<'db>]>;
    fn invalidate_references_to(&mut self, file_index: FileIndex);
}

pub trait FileState: fmt::Debug + Unpin {
    fn path(&self) -> &str;
    fn file(&self, reader: &dyn Vfs) -> Option<&(dyn File + 'static)>;
    fn maybe_loaded_file_mut(&mut self) -> Option<&mut dyn File>;
    fn set_file_index(&self, index: FileIndex);
    fn unload_and_return_invalidations(&mut self) -> Invalidations;
    fn add_invalidates(&self, file_index: FileIndex);
    fn take_invalidations(&mut self) -> Invalidations;
}

impl<F: File + Unpin> FileState for LanguageFileState<F> {
    fn path(&self) -> &str {
        &self.path
    }

    fn file(&self, file_system_reader: &dyn Vfs) -> Option<&(dyn File + 'static)> {
        match unsafe { &*self.state.get() } {
            InternalFileExistence::Unloaded => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                // It is extremely important to deal with the data given here before overwriting it
                // in `slot`. Otherwise we access memory that has different data structures.
                let file_index = file_index_cell.get().unwrap();
                if let Some(file) = file_system_reader.read_file(&self.path) {
                    unsafe { *self.state.get() = InternalFileExistence::Parsed(loader(file)) };
                } else {
                    unsafe { *self.state.get() = InternalFileExistence::Unloaded };
                }

                let file = self.file(file_system_reader);
                file.unwrap().set_file_index(file_index);
                file
            }
        }
    }

    fn maybe_loaded_file_mut(&mut self) -> Option<&mut dyn File> {
        match self.state.get_mut() {
            InternalFileExistence::Parsed(f) => Some(f),
            _ => None,
        }
    }

    fn set_file_index(&self, index: FileIndex) {
        match unsafe { &*self.state.get() } {
            InternalFileExistence::Unloaded => {}
            InternalFileExistence::Parsed(f) => f.set_file_index(index),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                file_index_cell.set(Some(index))
            }
        }
    }

    fn unload_and_return_invalidations(&mut self) -> Invalidations {
        let invalidates = std::mem::take(&mut self.invalidates);
        self.state = UnsafeCell::new(InternalFileExistence::Unloaded);
        invalidates
    }

    fn take_invalidations(&mut self) -> Invalidations {
        std::mem::take(&mut self.invalidates)
    }

    fn add_invalidates(&self, file_index: FileIndex) {
        self.invalidates.add(file_index)
    }
}

pub struct LanguageFileState<F: 'static> {
    path: String,
    // Unsafe, because the file is parsed lazily
    state: UnsafeCell<InternalFileExistence<F>>,
    invalidates: Invalidations,
}

impl<F> fmt::Debug for LanguageFileState<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("LanguageFileState")
            .field("path", &self.path)
            .field("state", unsafe { &*self.state.get() })
            .field("invalidates", &self.invalidates)
            .finish()
    }
}

impl<F: File> LanguageFileState<F> {
    pub fn new_parsed(path: String, file: F) -> Self {
        Self {
            path,
            state: UnsafeCell::new(InternalFileExistence::Parsed(file)),
            invalidates: Default::default(),
        }
    }

    fn new_unparsed(path: String, loader: LoadFileFunction<F>) -> Self {
        Self {
            path,
            state: UnsafeCell::new(InternalFileExistence::Unparsed(loader, Cell::new(None))),
            invalidates: Default::default(),
        }
    }
}

enum InternalFileExistence<F: 'static> {
    Unloaded,
    Unparsed(LoadFileFunction<F>, Cell<Option<FileIndex>>),
    Parsed(F),
}

impl<F> fmt::Debug for InternalFileExistence<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Intentionally remove the T here, because it's usually huge and we are usually not
        // interested in that while debugging.
        match *self {
            Self::Unloaded => write!(f, "Unloaded"),
            Self::Unparsed(_, _) => write!(f, "Unparsed"),
            Self::Parsed(_) => write!(f, "Parsed(_)"),
        }
    }
}
