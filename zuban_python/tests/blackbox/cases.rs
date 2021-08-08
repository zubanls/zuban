use std::path::PathBuf;
use std::collections::HashSet;
use zuban_python::{Script, Position};

pub struct TestFile {
    pub path: PathBuf,
    pub code: String,
}

#[derive(Debug)]
struct TestCase {
    line: usize,
    column: usize,
    type_: CaseType,
}

#[derive(Debug)]
enum CaseType {
    Infer(HashSet<String>),
}

impl TestFile {
    pub fn test(&self) {
        let mut project = zuban_python::Project::new("foo".to_owned());
        let script = Script::new(
            &mut project,
            Some(self.path.to_str().unwrap().to_owned()),
            Some(self.code.clone()),
        );
        for case in self.get_test_cases() {
            match case.type_ {
                CaseType::Infer(expected) => {
                    let actual: HashSet<_> = script
                        .infer_definition(Position::LineColumn(case.line, case.column))
                        .iter()
                        .map(|name| name.get_name().to_owned() + "()")
                        .collect();
                    assert_eq!(actual, expected);
                }
            }
        }
    }

    fn get_test_cases(&self) -> Vec<TestCase> {
        let mut cases = vec![];
        let lines: Vec<_> = self.code.split('\n').collect();
        for (line_nr, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("#? ") {
                let mut names: Vec<_> = trimmed[3..].split(" ").collect();
                let column = {
                    if let Ok(c) = names[0].parse() {
                        names.remove(0);
                        c
                    } else {
                        lines[line_nr + 1].len()
                    }
                };
                cases.push(TestCase {
                    // We need to add one, because we're evaluating the next line
                    line: line_nr + 1,
                    column,
                    type_: CaseType::Infer(names.iter().cloned().map(|x| x.to_owned()).collect()),
                });
            }
        }
        cases
    }
}

impl std::fmt::Debug for TestFile {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("TestFile").field("path", &self.path).finish()
    }
}
