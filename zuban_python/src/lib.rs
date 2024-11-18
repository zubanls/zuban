#![allow(clippy::nonminimal_bool)] // I don't like this rule
#![allow(clippy::too_many_arguments)] // TODO For now this is easier, but probably enable again

mod arguments;
mod config;
mod database;
mod diagnostics;
mod file;
mod format_data;
mod getitem;
mod imports;
mod inference_state;
mod inferred;
mod lines;
mod matching;
mod name;
mod node_ref;
mod params;
mod python_state;
mod type_;
mod type_helpers;
mod utils;
mod workspaces;

pub use config::{ExcludeRegex, ProjectOptions, PythonVersion, Settings, TypeCheckerFlags};
use database::{Database, FileIndex, PythonProject};
pub use diagnostics::DiagnosticConfig;
use file::{File, FileStateLoader, Leaf};
use inference_state::InferenceState;
use inferred::Inferred;
use matching::invalidate_protocol_cache;
use name::Names;
use parsa_python_cst::CodeIndex;

pub struct Project {
    db: Database,
}

impl Project {
    pub fn new(options: ProjectOptions) -> Self {
        let db = Database::new(get_loaders(), options);
        Self { db }
    }

    pub fn search(&self, _string: &str, _all_scopes: bool) {}

    pub fn complete_search(&self, _string: &str, _all_scopes: bool) {}

    pub fn load_in_memory_file(&mut self, path: Box<str>, code: Box<str>) {
        self.db.load_in_memory_file(path, code);
    }

    pub fn delete_directory(&mut self, path: &str) -> Result<(), String> {
        self.db.delete_directory(path)
    }

    pub fn unload_in_memory_file(&mut self, path: &str) -> Result<(), &'static str> {
        self.db.unload_in_memory_file(path)
    }

    pub fn unload_all_in_memory_files(&mut self) {
        // Mostly used for testing
        self.db.unload_all_in_memory_files()
    }

    pub fn diagnostics(&mut self, config: &DiagnosticConfig) -> Diagnostics<'_> {
        if self.db.project.settings.mypy_path.len() > 1 {
            debug!(
                "Has complex mypy path: {:?}",
                &self.db.project.settings.mypy_path
            );
        }
        let mut all_diagnostics: Vec<diagnostics::Diagnostic> = vec![];
        let mut checked_files = 0;
        let mut files_with_errors = 0;
        for directory in self.db.workspaces.directories_to_type_check() {
            let mut to_be_loaded = vec![];
            directory.walk(&mut |file_index_or_file| {
                if let Err(file) = file_index_or_file {
                    let path = file.relative_path(self.db.vfs.as_ref());
                    to_be_loaded.push((file.clone(), path));
                }
            });

            let maybe_skipped = |flags: &TypeCheckerFlags, path: &str| {
                let check_files = &self.db.project.settings.files_or_directories_to_check;
                !check_files.is_empty()
                    && !check_files
                        .iter()
                        .any(|p| self.db.vfs.is_sub_file_of(path, p))
                    || flags.excludes.iter().any(|e| e.regex.is_match(path))
            };
            for (file, path) in to_be_loaded {
                if !maybe_skipped(&self.db.project.flags, &path) {
                    self.db.load_file_from_workspace(file, false);
                }
            }

            let mut file_indexes = vec![];
            directory.walk(&mut |file_index| {
                if let Ok(file_index) = file_index {
                    file_indexes.push(file_index);
                }
            });
            'outer: for file_index in file_indexes {
                let python_file = self.db.loaded_python_file(file_index);
                let relative = python_file
                    .file_entry(&self.db)
                    .relative_path(self.db.vfs.as_ref());
                if maybe_skipped(python_file.flags(&self.db), &relative) {
                    continue 'outer;
                }
                checked_files += 1;
                let mut issues = python_file.diagnostics(&self.db, config).into_vec();
                if !issues.is_empty() {
                    files_with_errors += 1;
                    all_diagnostics.append(&mut issues)
                }
            }
        }
        invalidate_protocol_cache();
        Diagnostics {
            checked_files,
            files_with_errors,
            issues: all_diagnostics.into_boxed_slice(),
        }
    }

    /// This function is mostly for tests and should therefore not be used for something
    /// stable. We would have to ensure first it works everywhere.
    /// It currently is for example a big issue that HashableRawStr used in the name binder is very
    /// unsafe and will lead to SEGFAULTS if the original project is not kept.
    pub fn try_to_reuse_project_resources_for_tests(&self, options: ProjectOptions) -> Self {
        let db = self
            .db
            .try_to_reuse_project_resources_for_tests(get_loaders(), options);
        Project { db }
    }
}

fn get_loaders() -> Box<[Box<dyn FileStateLoader>; 1]> {
    Box::new([Box::<file::PythonFileLoader>::default() as Box<_>])
}

#[derive(Debug, Clone, Copy)]
pub enum Position {
    Byte(usize),
    LineColumn(usize, usize),
}

pub struct Script<'a> {
    project: &'a mut Project,
    file_index: FileIndex,
}

impl<'a> Script<'a> {
    pub fn new(project: &'a mut Project, path: Option<Box<str>>, code: Option<Box<str>>) -> Self {
        let db = &mut project.db;
        db.acquire();
        let file_index = match path {
            Some(path) => {
                if let Some(code) = code {
                    db.load_in_memory_file(path, code)
                } else {
                    db.in_memory_file(&path)
                        .or_else(|| unimplemented!())
                        .unwrap()
                }
            }
            None => unimplemented!(),
        };
        Self {
            project,
            file_index,
        }
    }

    fn to_byte_position(&self, position: Position) -> CodeIndex {
        match position {
            Position::Byte(pos) => pos as u32,
            Position::LineColumn(line, column) => self.file().line_column_to_byte(line, column),
        }
    }

    fn file(&self) -> &dyn file::File {
        self.project.db.loaded_file(self.file_index)
    }

    fn leaf(&self, position: Position) -> Leaf {
        let pos = self.to_byte_position(position);
        let leaf = self.file().leaf(&self.project.db, pos);
        debug!("File {}", self.file().file_path(&self.project.db));
        debug!("Position {position:?} is on leaf {leaf:?}");
        leaf
    }

    pub fn complete(&self, _position: Position) {}

    /*
    pub fn infer_definition<C: Fn(&dyn ValueName<'a>) -> T, T>(
        &'a self,
        callable: &C,
        position: Position,
    ) -> impl Iterator<Item = T> {
        let i_s = InferenceState::new(&self.project.db);
        match self.leaf(position) {
            Leaf::Name(name) => name.infer(),
            Leaf::Number => unimplemented!(),
            Leaf::Keyword(keyword) => self.file().infer_operator_leaf(&self.project.db, keyword),
            Leaf::None | Leaf::String => unimplemented!(),
        }
    }
    */

    /*
    pub fn infer_implementation(&self, position: Position) -> ValueNames {
        let names = self.infer_definition(position);
        //self.file.implementation(names);
        unimplemented!()
    }
    */

    pub fn goto_definition(&self, position: Position, _follow_imports: bool) -> Names {
        match self.leaf(position) {
            Leaf::Name(name) => name.goto(),
            Leaf::Number => unimplemented!(),
            Leaf::Keyword(_keyword) => unimplemented!(),
            Leaf::None | Leaf::String => vec![],
        }
    }

    pub fn goto_implementation(&self, position: Position, follow_imports: bool) -> Names {
        let names = self.goto_definition(position, follow_imports);
        self.file().implementation(names)
    }

    pub fn search(&self, _text: String, _all_scopes: bool, _fuzzy: bool) {}

    pub fn complete_search(&self, _text: String, _all_scopes: bool, _fuzzy: bool) {}

    pub fn help(&self, _position: Position) {}

    pub fn references(&self, _position: Position /*, scope='project'*/) {}

    pub fn signatures(&self, _position: Position) {}

    pub fn context(&self, _position: Position) {}

    pub fn names(&self /*all_scopes=False, definitions=True, references=False*/) {}

    pub fn diagnostics(&self, config: &DiagnosticConfig) -> Box<[diagnostics::Diagnostic<'_>]> {
        self.file().diagnostics(&self.project.db, config)
    }

    pub fn errors(&self) {}

    pub fn rename(&self, _position: Position, _new_name: &str) {}

    pub fn extract_variable(
        &self,
        _position: Position,
        _new_name: &str,
        _until_line: Option<usize>,
        _until_column: Option<usize>,
    ) {
    }

    pub fn extract_function(
        &self,
        _position: Position,
        _new_name: &str,
        _until_line: Option<usize>,
        _until_column: Option<usize>,
    ) {
    }

    pub fn inline(&self, _position: Position) {}

    /*
    pub fn selection_ranges() {
    }

    pub fn errors() {
    }
    */
}

impl<'a> Drop for Script<'a> {
    fn drop(&mut self) {
        self.project.db.release()
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum ValueKind {
    Unknown = 0,
    // Taken from LSP, unused kinds are commented
    //File = 1,
    Module = 2,
    Namespace = 3,
    //Package = 4,
    Class = 5,
    Method = 6,
    Property = 7,
    Field = 8,
    //Constructor = 9,
    //Enum = 10,
    //Interface = 11,
    Function = 12,
    //Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    Bool = 17,
    Array = 18,
    Object = 19, // From JavaScript objects -> Basically an instance
    //Key = 20,
    Null = 21,
    //EnumMember = 22,
    //Struct = 23,
    //Event = 24,
    //Operator = 25,
    TypeParameter = 26,
}

pub struct Diagnostics<'a> {
    pub checked_files: usize,
    pub files_with_errors: usize,
    pub issues: Box<[diagnostics::Diagnostic<'a>]>,
}
