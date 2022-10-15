#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(clippy::needless_option_as_deref)] // This is simply wrong in some cases
#![allow(clippy::too_many_arguments)] // For now this is easier, but probably enable again
#![allow(mutable_borrow_reservation_conflict)]

mod arguments;
mod database;
mod diagnostics;
mod file;
mod file_state;
mod getitem;
mod imports;
mod inference_state;
mod inferred;
mod lines;
mod matching;
mod name;
mod node_ref;
mod python_state;
mod utils;
mod value;
mod workspaces;

use database::{Database, FileIndex};
pub use diagnostics::DiagnosticConfig;
use file_state::{Leaf, PythonFileLoader};
use inference_state::InferenceState;
use inferred::Inferred;
use name::{Names, ValueName};
use parsa_python_ast::CodeIndex;
pub use value::ValueKind;
use workspaces::Workspaces;

pub enum ProjectType {
    PythonProject(PythonProject),
}

pub struct Project {
    type_: ProjectType,
    db: Database,
}

impl Project {
    pub fn new(path: String) -> Self {
        let loaders = Box::new([Box::new(PythonFileLoader::default()) as Box<_>]);
        // TODO use a real sys path
        let sys_path = vec![
            "../typeshed/stdlib".to_owned(),
            "../typeshed/stubs".to_owned(),
            "/usr/lib/python3/dist-packages".to_owned(),
            "/usr/local/lib/python3.8/dist-packages/pip-20.0.2-py3.8.egg".to_owned(),
            "/usr/lib/python3.8".to_owned(),
            "/home/dave/.local/lib/python3.8/site-packages".to_owned(),
            "/usr/local/lib/python3.8/dist-packages".to_owned(),
        ];
        let mut workspaces = Workspaces::default();
        for p in &sys_path {
            workspaces.add(loaders.as_ref(), p.to_owned())
        }
        workspaces.add(loaders.as_ref(), path.clone());
        let db = Database::new(loaders, workspaces);
        Self {
            type_: ProjectType::PythonProject(PythonProject {
                path,
                sys_path,
                is_django: false,
            }),
            db,
        }
    }

    pub fn search(&self, string: &str, all_scopes: bool) {}

    pub fn complete_search(&self, string: &str, all_scopes: bool) {}

    pub fn load_in_memory_file(&mut self, path: String, code: String) {
        self.db.load_in_memory_file(path, code);
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
            .root()
            .clone()
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

pub struct PythonProject {
    path: String,
    sys_path: Vec<String>,
    is_django: bool,
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
    pub fn new(project: &'a mut Project, path: Option<String>, code: Option<String>) -> Self {
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

    fn file(&self) -> &dyn file_state::File {
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

    pub fn infer_definition<C: Fn(&dyn ValueName<'a>) -> T, T>(
        &'a self,
        callable: &C,
        position: Position,
    ) -> impl Iterator<Item = T> {
        let mut i_s = InferenceState::new(&self.project.db);
        match self.leaf(position) {
            Leaf::Name(name) => name.infer(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => self.file().infer_operator_leaf(&self.project.db, keyword),
            Leaf::None | Leaf::String => todo!(),
        }
        .run_on_value_names(&mut i_s, callable)
    }

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

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
