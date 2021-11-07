use crate::database::{Database, FileIndex, Locality};
use crate::file::PythonFile;
use crate::inferred::Inferred;
use crate::name::{Name, Names};
use parsa_python_ast::{CodeIndex, Keyword, NodeIndex};
use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::fmt;
use std::fs;
use std::pin::Pin;

type InvalidatedDependencies = Vec<FileIndex>;
type LoadFileFunction<F> = &'static dyn Fn(String) -> F;

pub trait VirtualFileSystemReader {
    fn read_file(&self, path: &str) -> Option<String>;
}

#[derive(Default)]
pub struct FileSystemReader {}

impl VirtualFileSystemReader for FileSystemReader {
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

    fn get_inexistent_file_state(&self, path: String) -> Pin<Box<dyn FileState>>;
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

    fn get_inexistent_file_state(&self, path: String) -> Pin<Box<dyn FileState>> {
        Box::pin(LanguageFileState::<PythonFile>::new_does_not_exist(path))
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

    fn line_column_to_byte(&self, line: usize, column: usize) -> CodeIndex;
    fn byte_to_line_column(&self, byte: CodeIndex) -> (usize, usize);

    fn file_path<'db>(&self, database: &'db Database) -> &'db str {
        database.file_path(self.file_index())
    }
}

pub trait FileState: fmt::Debug {
    fn get_path(&self) -> &str;
    fn file(&self, database: &Database) -> Option<&(dyn File + 'static)>;
    fn set_file_index(&self, index: FileIndex);
}

impl<F: File> FileState for LanguageFileState<F> {
    fn get_path(&self) -> &str {
        &self.path
    }

    fn file(&self, database: &Database) -> Option<&(dyn File + 'static)> {
        match unsafe { &*self.state.get() } {
            InternalFileExistence::Missing => None,
            InternalFileExistence::Parsed(f) => Some(f),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                // It is extremely important to deal with the data given here before overwriting it
                // in `slot`. Otherwise we access memory that has different data structures.
                let file_index = file_index_cell.get().unwrap();
                if let Some(file) = database.file_system_reader.read_file(&self.path) {
                    unsafe { *self.state.get() = InternalFileExistence::Parsed(loader(file)) };
                } else {
                    unsafe { *self.state.get() = InternalFileExistence::Missing };
                }

                let file = self.file(database);
                file.unwrap().set_file_index(file_index);
                file
            }
        }
    }

    fn set_file_index(&self, index: FileIndex) {
        match unsafe { &*self.state.get() } {
            InternalFileExistence::Missing => {}
            InternalFileExistence::Parsed(f) => f.set_file_index(index),
            InternalFileExistence::Unparsed(loader, file_index_cell) => {
                file_index_cell.set(Some(index))
            }
        }
    }
}

pub struct LanguageFileState<F: 'static> {
    path: String,
    // Unsafe, because the file is parsed lazily
    state: UnsafeCell<InternalFileExistence<F>>,
    invalidates: Vec<FileIndex>,
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
    fn new_parsed(path: String, file: F) -> Self {
        Self {
            path,
            state: UnsafeCell::new(InternalFileExistence::Parsed(file)),
            invalidates: vec![],
        }
    }

    fn new_unparsed(path: String, loader: LoadFileFunction<F>) -> Self {
        Self {
            path,
            state: UnsafeCell::new(InternalFileExistence::Unparsed(loader, Cell::new(None))),
            invalidates: vec![],
        }
    }

    fn new_does_not_exist(path: String) -> Self {
        Self {
            path,
            state: UnsafeCell::new(InternalFileExistence::Missing),
            invalidates: vec![],
        }
    }
}

enum InternalFileExistence<F: 'static> {
    Missing,
    Unparsed(LoadFileFunction<F>, Cell<Option<FileIndex>>),
    Parsed(F),
}

impl<F> fmt::Debug for InternalFileExistence<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Intentionally remove the T here, because it's usually huge and we are usually not
        // interested in that while debugging.
        match *self {
            Self::Missing => write!(f, "DoesNotExist"),
            Self::Unparsed(_, _) => write!(f, "Unparsed"),
            Self::Parsed(_) => write!(f, "Parsed(_)"),
        }
    }
}

#[derive(Debug)]
pub struct Issue {
    issue_id: u32,
    tree_node: NodeIndex,
    locality: Locality,
}
