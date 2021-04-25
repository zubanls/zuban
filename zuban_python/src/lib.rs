#![allow(unused_variables)]
#![allow(dead_code)]

mod cache;
mod module;
mod name;
mod value;

use std::path::PathBuf;
use parsa::CodeIndex;
use module::{Leaf};
use name::{Names, ValueNames};

pub enum Project {
    PythonProject(PythonProject),
}

impl Project {
    pub fn new(path: String) -> Self {
        Self::PythonProject(PythonProject {
            path,
            sys_path: vec!(),
            is_django: false,
            state_db: Default::default(),
        })
    }

    fn search(&self, string: &str, all_scopes: bool) {
    }
    fn complete_search(&self, string: &str, all_scopes: bool) {
    }

    fn get_state(&self) -> &cache::StateDB {
        // TODO cleanup
        match self {
            Project::PythonProject(x) => &x.state_db,
        }
    }
}

pub struct PythonProject {
    path: String,
    //environment_path: String,
    sys_path: Vec<String>,
    is_django: bool,
    state_db: cache::StateDB,
}

pub enum Position {
    Byte(usize),
    LineColumn(usize, usize),
}

pub struct Script<'a> {
    project: &'a mut Project,
    module: Box<dyn module::Module>,
}

impl<'a> Script<'a> {
    pub fn new(project: &'a mut Project, path: Option<PathBuf>, code: Option<String>) -> Self {
        let state = project.get_state();
        let module = state.get_module_by_path(path.unwrap().canonicalize().unwrap());
        todo!();
        //Self {project, module}
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
        self.module.get_leaf(self.project.get_state(), pos)
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
        //self.module.get_implementation(names);
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
        self.module.get_implementation(names)
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
