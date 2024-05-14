#![allow(unused_variables)] // TODO remove this
#![allow(clippy::needless_option_as_deref)] // This is simply wrong in some cases
#![allow(clippy::too_many_arguments)] // TODO For now this is easier, but probably enable again
#![allow(clippy::single_match)] // TODO this is probably just practical during development

mod arguments;
mod config;
mod database;
mod diagnostics;
mod file;
mod getitem;
mod imports;
mod inference_state;
mod inferred;
mod lines;
mod matching;
mod name;
mod node_ref;
mod python_state;
mod type_;
mod type_helpers;
mod utils;
mod workspaces;

use database::{Database, FileIndex, PythonProject};
pub use diagnostics::DiagnosticConfig;
use file::Leaf;
use inference_state::InferenceState;
use inferred::Inferred;
use name::Names;
use parsa_python_cst::CodeIndex;

pub struct Project {
    db: Database,
}

#[derive(Clone)]
pub struct ProjectOptions {
    pub path: Box<str>,
    pub flags: TypeCheckerFlags,
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct TypeCheckerFlags {
    pub strict_optional: bool,
    pub strict_equality: bool,
    pub implicit_optional: bool,
    pub check_untyped_defs: bool,

    pub disallow_untyped_defs: bool,
    pub disallow_untyped_calls: bool,
    pub disallow_untyped_decorators: bool,
    pub disallow_any_generics: bool,
    pub disallow_any_decorated: bool,
    pub disallow_any_explicit: bool,
    pub disallow_any_unimported: bool,
    pub disallow_any_expr: bool,
    pub disallow_subclassing_any: bool,
    pub disallow_incomplete_defs: bool,
    pub allow_untyped_globals: bool,
    pub allow_empty_bodies: bool,
    pub warn_unreachable: bool,
    pub warn_redundant_casts: bool,
    pub warn_return_any: bool,
    pub warn_no_return: bool,
    pub local_partial_types: bool,
    pub no_implicit_reexport: bool,
    pub disable_bytearray_promotion: bool,
    pub disable_memoryview_promotion: bool,

    pub platform: Option<String>,
    pub enabled_error_codes: Vec<String>,
    pub disabled_error_codes: Vec<String>,
    pub python_version: PythonVersion,
    pub always_true_symbols: Vec<String>,
    pub always_false_symbols: Vec<String>,

    pub extra_checks: bool,
    pub mypy_compatible: bool,
}

impl Default for TypeCheckerFlags {
    fn default() -> Self {
        Self {
            strict_optional: true,
            strict_equality: false,
            implicit_optional: false,
            check_untyped_defs: false,
            disallow_untyped_defs: false,
            disallow_untyped_calls: false,
            disallow_untyped_decorators: false,
            disallow_any_generics: false,
            disallow_any_decorated: false,
            disallow_any_explicit: false,
            disallow_any_unimported: false,
            disallow_any_expr: false,
            disallow_subclassing_any: false,
            disallow_incomplete_defs: false,
            allow_untyped_globals: false,
            allow_empty_bodies: false,
            warn_unreachable: false,
            warn_redundant_casts: false,
            warn_return_any: false,
            warn_no_return: true,
            local_partial_types: false,
            no_implicit_reexport: false,
            disable_bytearray_promotion: false,
            disable_memoryview_promotion: false,
            platform: None,
            python_version: PythonVersion::new(3, 12),
            always_true_symbols: vec![],
            always_false_symbols: vec![],
            enabled_error_codes: vec![],
            disabled_error_codes: vec![],
            extra_checks: false,
            mypy_compatible: false,
        }
    }
}

impl TypeCheckerFlags {
    pub fn strict() -> Self {
        Self {
            strict_equality: true,
            check_untyped_defs: true,
            disallow_untyped_defs: true,
            disallow_untyped_calls: true,
            disallow_any_generics: true,
            disallow_any_decorated: true,
            disallow_any_explicit: true,
            disallow_subclassing_any: true,
            disallow_incomplete_defs: true,
            warn_redundant_casts: true,
            warn_return_any: true,
            ..Self::default()
        }
    }

    fn computed_platform(&self) -> &str {
        self.platform.as_deref().unwrap_or("posix")
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct PythonVersion {
    major: usize,
    minor: usize,
}

impl PythonVersion {
    pub fn new(major: usize, minor: usize) -> Self {
        Self { major, minor }
    }

    pub fn at_least_3_dot(&self, minor: usize) -> bool {
        self.major >= 3 && self.minor >= minor
    }
}

impl Project {
    pub fn new(options: ProjectOptions) -> Self {
        let loaders = Box::new([Box::<file::PythonFileLoader>::default() as Box<_>]);
        // TODO use a real sys path
        let sys_path = vec![
            "../typeshed/stdlib".into(),
            "../typeshed/stubs/mypy-extensions".into(),
            //"../typeshed/stubs".into(),
            //"/usr/lib/python3/dist-packages".into(),
            //"/usr/local/lib/python3.8/dist-packages/pip-20.0.2-py3.8.egg".into(),
            //"/usr/lib/python3.8".into(),
            //"/home/dave/.local/lib/python3.8/site-packages".into(),
            //"/usr/local/lib/python3.8/dist-packages".into(),
        ];
        let db = Database::new(
            loaders,
            options.path,
            PythonProject {
                sys_path,
                flags: options.flags,
            },
        );
        Self { db }
    }

    pub fn search(&self, string: &str, all_scopes: bool) {}

    pub fn complete_search(&self, string: &str, all_scopes: bool) {}

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

    pub fn diagnostics(&mut self, config: &DiagnosticConfig) -> Box<[diagnostics::Diagnostic<'_>]> {
        let mut all_diagnostics: Vec<diagnostics::Diagnostic> = vec![];
        let mut file_indexes = vec![];
        self.db
            .workspaces
            .last()
            .directory()
            .for_each_file(&mut |file_index| {
                file_indexes.push(file_index);
            });
        for file_index in file_indexes {
            let file = self.db.loaded_file(file_index);
            debug!(
                "Calculate Diagnostics for {} ({})",
                file.file_path(&self.db),
                file.file_index(),
            );

            let array: [i32; 3] = [0; 3];
            all_diagnostics.append(&mut file.diagnostics(&self.db, config).into_vec())
        }
        all_diagnostics.into_boxed_slice()
    }
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
                        .or_else(|| {
                            let file_index = db.file_state_index_by_path(&path);
                            todo!()
                        })
                        .unwrap()
                }
            }
            None => todo!(),
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

    pub fn complete(&self, position: Position) {}

    /*
    pub fn infer_definition<C: Fn(&dyn ValueName<'a>) -> T, T>(
        &'a self,
        callable: &C,
        position: Position,
    ) -> impl Iterator<Item = T> {
        let i_s = InferenceState::new(&self.project.db);
        match self.leaf(position) {
            Leaf::Name(name) => name.infer(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => self.file().infer_operator_leaf(&self.project.db, keyword),
            Leaf::None | Leaf::String => todo!(),
        }
    }
    */

    /*
    pub fn infer_implementation(&self, position: Position) -> ValueNames {
        let names = self.infer_definition(position);
        //self.file.implementation(names);
        todo!()
    }
    */

    pub fn goto_definition(&self, position: Position, follow_imports: bool) -> Names {
        match self.leaf(position) {
            Leaf::Name(name) => name.goto(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => todo!(),
            Leaf::None | Leaf::String => vec![],
        }
    }

    pub fn goto_implementation(&self, position: Position, follow_imports: bool) -> Names {
        let names = self.goto_definition(position, follow_imports);
        self.file().implementation(names)
    }

    pub fn search(&self, text: String, all_scopes: bool, fuzzy: bool) {}

    pub fn complete_search(&self, text: String, all_scopes: bool, fuzzy: bool) {}

    pub fn help(&self, position: Position) {}

    pub fn references(&self, position: Position /*, scope='project'*/) {}

    pub fn signatures(&self, position: Position) {}

    pub fn context(&self, position: Position) {}

    pub fn names(&self /*all_scopes=False, definitions=True, references=False*/) {}

    pub fn diagnostics(&self, config: &DiagnosticConfig) -> Box<[diagnostics::Diagnostic<'_>]> {
        self.file().diagnostics(&self.project.db, config)
    }

    pub fn errors(&self) {}

    pub fn rename(&self, position: Position, new_name: &str) {}

    pub fn extract_variable(
        &self,
        position: Position,
        new_name: &str,
        until_line: Option<usize>,
        until_column: Option<usize>,
    ) {
    }

    pub fn extract_function(
        &self,
        position: Position,
        new_name: &str,
        until_line: Option<usize>,
        until_column: Option<usize>,
    ) {
    }

    pub fn inline(&self, position: Position) {}

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

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
