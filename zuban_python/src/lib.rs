#![allow(unused_variables)]
#![allow(dead_code)]

mod database;
mod file;
mod name;
mod value;
mod utils;

use parsa::CodeIndex;
use file::{Leaf, PythonFileLoader};
use name::{Names, ValueNames};
use database::{FileIndex, Database};

pub enum ProjectType {
    PythonProject(PythonProject),
}

pub struct Project {
    type_: ProjectType,
    database: Database,
}

impl Project {
    pub fn new(path: String) -> Self {
        let loaders = vec!(Box::new(PythonFileLoader::default()) as Box<_>);
        Self {
            type_: ProjectType::PythonProject(PythonProject {
                path,
                sys_path: vec!(),
                is_django: false,
            }),
            database: Database::new(loaders.into_boxed_slice()),
        }
    }

    pub fn search(&self, string: &str, all_scopes: bool) {
    }

    pub fn complete_search(&self, string: &str, all_scopes: bool) {
    }
}

pub struct PythonProject {
    path: String,
    sys_path: Vec<String>,
    is_django: bool,
}

#[derive(Clone, Copy)]
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
        let path = path.unwrap();
        let file_index = database.get_file_index_by_path(&path);
        let file_index = file_index.unwrap_or_else(|| database.load_file(path, code.unwrap()));
        Self {project, file_index}
    }

    fn to_byte_position(&self, position: Position) -> CodeIndex {
        match position {
            Position::Byte(pos) => pos as u32,
            Position::LineColumn(line, column) => {
                todo!();
            },
        }
    }

    fn get_file(&self) -> &dyn file::File {
        self.project.database.get_file(self.file_index)
    }

    fn get_leaf(&self, position: Position) -> Leaf {
        let pos = self.to_byte_position(position);
        self.get_file().get_leaf(&self.project.database, pos)
    }

    pub fn complete(&self, position: Position) {
    }

    pub fn infer_definition(&self, position: Position) -> ValueNames {
        dbg!(self.get_leaf(position));
        match self.get_leaf(position) {
            Leaf::Name(name) => name.infer(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => todo!(),
            Leaf::Other | Leaf::None | Leaf::String => vec!(),
        }
    }

    pub fn infer_implementation(&self, position: Position) -> ValueNames {
        let names = self.infer_definition(position);
        //self.file.get_implementation(names);
        todo!()
    }

    pub fn goto_definition(&self, position: Position, follow_imports: bool) -> Names {
        match self.get_leaf(position) {
            Leaf::Name(name) => name.goto(),
            Leaf::Number => todo!(),
            Leaf::Keyword(keyword) => todo!(),
            Leaf::Other | Leaf::None | Leaf::String => vec!(),
        }
    }

    pub fn goto_implementation(&self, position: Position, follow_imports: bool) -> Names {
        let names = self.goto_definition(position, follow_imports);
        self.get_file().get_implementation(names)
    }

    pub fn search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    pub fn complete_search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    pub fn help(&self, position: Position) {
    }

    pub fn get_references(&self, position: Position/*, scope='project'*/) {
    }

    pub fn get_signatures(&self, position: Position) {
    }

    pub fn get_context(&self, position: Position) {
    }

    pub fn get_names(&self, /*all_scopes=False, definitions=True, references=False*/) {
    }

    pub fn get_syntax_errors(&self) {
    }

    pub fn get_errors(&self) {
    }

    pub fn rename(&self, position: Position, new_name: &str) {
    }

    pub fn extract_variable(&self, position: Position, new_name: &str,
                        until_line: Option<usize>, until_column: Option<usize>) {
    }

    pub fn extract_function(&self, position: Position, new_name: &str,
                        until_line: Option<usize>, until_column: Option<usize>) {
    }

    pub fn inline(&self, position: Position) {
    }

    /*
    pub fn get_selection_ranges() {
    }

    pub fn get_errors() {
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
