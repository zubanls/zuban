#![allow(unused_variables)]
#![allow(dead_code)]

mod cache;
use std::path::PathBuf;

pub enum Project {
    PythonProject(PythonProject),
}

impl Project {
    pub fn new(path: String) -> Self {
        Self::PythonProject(PythonProject {
            path,
            sys_path: vec!(),
            is_django: false,
            database: Default::default(),
        })
    }

    fn search(&self, string: &str, all_scopes: bool) {
    }
    fn complete_search(&self, string: &str, all_scopes: bool) {
    }

    fn get_state(&self) -> &cache::StateDB {
        // TODO cleanup
        match self {
            Project::PythonProject(x) => &x.database,
        }
    }
}

pub struct PythonProject {
    path: String,
    //environment_path: String,
    sys_path: Vec<String>,
    is_django: bool,
    database: cache::StateDB,
}

pub struct Script<'a> {
    project: &'a mut Project,
    path: Option<PathBuf>,
    code: Option<String>,
}

impl<'a> Script<'a> {
    pub fn new(project: &'a mut Project, path: Option<PathBuf>, code: Option<String>) -> Self {
        Self {project, path, code}
    }

    fn complete(&self, line: usize, column: usize) {
    }

    fn infer_definition(&self, line: usize, column: usize) {
    }
    fn infer_implementation(&self, line: usize, column: usize) {
    }

    fn goto_definition(&self, line: usize, column: usize, follow_imports: bool) {
    }
    fn goto_implementation(&self, line: usize, column: usize, follow_imports: bool) {
    }

    fn search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    fn complete_search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    fn help(&self, line: usize, column: usize) {
    }

    fn get_references(&self, line: usize, column: usize/*, scope='project'*/) {
    }

    fn get_signatures(&self, line: usize, column: usize) {
    }

    fn get_context(&self, line: usize, column: usize) {
    }

    fn get_names(&self, /*all_scopes=False, definitions=True, references=False*/) {
    }

    fn get_syntax_errors(&self) {
    }

    fn get_errors(&self) {
    }

    fn rename(&self, line: usize, column: usize, new_name: &str) {
    }

    fn extract_variable(&self, line: usize, column: usize, new_name: &str,
                        until_line: Option<usize>, until_column: Option<usize>) {
    }

    fn extract_function(&self, line: usize, column: usize, new_name: &str,
                        until_line: Option<usize>, until_column: Option<usize>) {
    }

    fn inline(&self, line: usize, column: usize) {
    }

    /*
    fn get_selection_ranges() {
    }

    fn get_errors() {
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
