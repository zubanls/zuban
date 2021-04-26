#![allow(unused_variables)]
#![allow(dead_code)]

mod cache;
mod file;
mod name;
mod value;

use std::path::PathBuf;
use parsa::CodeIndex;
use file::{Leaf};
use name::{Names, ValueNames};

pub enum ProjectType {
    PythonProject(PythonProject),
}

pub struct Project {
    type_: ProjectType,
    database: cache::Database,
}

impl Project {
    pub fn new(path: String) -> Self {
        Self {
            type_: ProjectType::PythonProject(PythonProject {
                path,
                sys_path: vec!(),
                is_django: false,
            }),
            database: Default::default(),
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

pub enum Position {
    Byte(usize),
    LineColumn(usize, usize),
}

pub struct Script<'a> {
    project: &'a mut Project,
    file: &'a dyn file::File,
}

impl<'a> Script<'a> {
    pub fn new(project: &'a mut Project, path: Option<PathBuf>, code: Option<String>) -> Self {
        let file = project.database.get_file_by_path(path.unwrap().canonicalize().unwrap());
        todo!();
        //Self {project, file}
    }

    fn to_byte_position(&self, position: Position) -> CodeIndex {
        match position {
            Position::Byte(pos) => pos as u32,
            Position::LineColumn(line, column) => {
                todo!();
            },
        }
    }

    fn get_leaf(&self, position: Position) -> Leaf {
        let pos = self.to_byte_position(position);
        self.file.get_leaf(&self.project.database, pos)
    }

    pub fn complete(&self, position: Position) {
    }

    pub fn infer_definition(&self, position: Position) -> ValueNames {
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
        self.file.get_implementation(names)
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

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
