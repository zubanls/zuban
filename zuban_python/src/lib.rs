#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(clippy::while_let_on_iterator)] // This is simply wrong in some cases
#![allow(clippy::collapsible_if)]
#![allow(mutable_borrow_reservation_conflict)]

mod arguments;
mod database;
mod file;
mod file_state;
mod generics;
mod getitem;
mod imports;
mod inference_state;
mod inferred;
mod name;
mod name_binder;
mod python_state;
mod utils;
mod value;

use database::{Database, FileIndex, Workspace};
use file_state::{Leaf, PythonFileLoader};
use inference_state::InferenceState;
use name::{Names, ValueName};
use parsa_python_ast::CodeIndex;
pub use value::ValueKind;

pub enum ProjectType {
    PythonProject(PythonProject),
}

pub struct Project {
    type_: ProjectType,
    database: Database,
}

impl Project {
    pub fn new(path: String) -> Self {
        let loaders = Box::new([Box::new(PythonFileLoader::default()) as Box<_>]);
        // TODO use a real sys path
        let sys_path = vec![
            "/usr/lib/python3/dist-packages".to_owned(),
            "/usr/local/lib/python3.8/dist-packages/pip-20.0.2-py3.8.egg".to_owned(),
            "/usr/lib/python3.8".to_owned(),
            "/home/dave/.local/lib/python3.8/site-packages".to_owned(),
            "/usr/local/lib/python3.8/dist-packages".to_owned(),
        ];
        let workspaces = sys_path
            .iter()
            .map(|s| Workspace::new(loaders.as_ref(), s.to_owned()))
            .collect();
        let database = Database::new(loaders, workspaces);
        Self {
            type_: ProjectType::PythonProject(PythonProject {
                path,
                sys_path,
                is_django: false,
            }),
            database,
        }
    }

    pub fn search(&self, string: &str, all_scopes: bool) {}

    pub fn complete_search(&self, string: &str, all_scopes: bool) {}

    pub fn add_in_memory_file(&mut self, path: String, code: String) {
        self.internal_add_in_memory_file(path, code);
    }

    fn internal_add_in_memory_file(&mut self, path: String, code: String) -> FileIndex {
        let file_index = self.database.load_file(path.clone(), code);
        self.database.in_memory_files.insert(path, file_index);
        file_index
    }

    pub fn unload_in_memory_file(&mut self, path: &str) -> Result<(), &'static str> {
        self.database.unload_in_memory_file(path)
    }

    pub fn unload_all_in_memory_files(&mut self) {
        // Mostly used for testing
        self.database.unload_all_in_memory_files()
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
        let database = &mut project.database;
        database.acquire();
        let file_index = match path {
            Some(path) => {
                if let Some(code) = code {
                    project.internal_add_in_memory_file(path, code)
                } else {
                    let file_index = database.file_state_index_by_path(&path);
                    file_index.unwrap_or_else(|| database.load_file(path, code.unwrap()));
                    todo!()
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
        self.project
            .database
            .file_state(self.file_index)
            .file(&self.project.database)
            .unwrap()
    }

    fn leaf(&self, position: Position) -> Leaf {
        let pos = self.to_byte_position(position);
        let leaf = self.file().leaf(&self.project.database, pos);
        debug!("File {}", self.file().file_path(&self.project.database));
        debug!("Position {:?} is on leaf {:?}", position, leaf);
        leaf
    }

    pub fn complete(&self, position: Position) {}

    pub fn infer_definition<C: Fn(&dyn ValueName<'a>) -> T, T>(
        &'a self,
        callable: &C,
        position: Position,
    ) -> impl Iterator<Item = T> {
        let mut i_s = InferenceState::new(&self.project.database);
        match self.leaf(position) {
            Leaf::Name(name) => name.infer(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => self
                .file()
                .infer_operator_leaf(&self.project.database, keyword),
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

    pub fn syntax_errors(&self) {}

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
        self.project.database.release()
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
