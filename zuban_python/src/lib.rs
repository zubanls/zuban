#![allow(unused_variables)]
#![allow(dead_code)]

mod cache;

enum Project {
    PythonProject(PythonProject),
}

impl Project {
    fn search(&self, string: &str, all_scopes: bool) {
    }
    fn complete_search(&self, string: &str, all_scopes: bool) {
    }
}

struct PythonProject {
    path: String,
    //environment_path: String,
    sys_path: Vec<String>,
    is_django: bool,
    database: cache::StateDB,
}

struct Script {
}

impl Script {
    fn _new(code: String, path: &str, project: Project) {
    }

    fn complete(&self, line: usize, column: usize) {
    }

    fn infer(&self, line: usize, column: usize/*, only_stubs=False, prefer_stubs=False*/) {
    }

    fn goto(&self, line: usize, column: usize/*, follow_imports=False, follow_builtin_imports=False,
            only_stubs=False, prefer_stubs=False*/) {
    }

    fn search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    fn complete_search(&self, text: String, all_scopes: bool, fuzzy: bool) {
    }

    fn help(&self, line: usize, column: usize) {
    }

    fn get_references(&self, line: usize, column: usize/*, include_builtins=True, scope='project'*/) {
    }

    fn get_signatures(&self, line: usize, column: usize) {
    }

    fn get_context(&self, line: usize, column: usize) {
    }

    fn get_names(&self, /*all_scopes=False, definitions=True, references=False*/) {
    }

    fn get_syntax_errors(&self) {
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
