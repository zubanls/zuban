use std::collections::HashSet;
use std::path::PathBuf;
use zuban_python::{Position, Script, ValueKind};

use crate::Filter;

pub struct TestFile<'a> {
    pub path: PathBuf,
    pub code: String,
    pub filters: &'a [Filter],
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
    Complete(Vec<String>),
}

impl TestFile<'_> {
    pub fn test(&self, project: &mut zuban_python::Project) -> (usize, usize) {
        let script = Script::new(
            project,
            Some(self.path.to_str().unwrap().to_owned()),
            Some(self.code.clone()),
        );
        let cases = self.find_test_cases();
        let full_count = cases.len();
        let mut ran_count = 0;
        for case in cases {
            let file_name = self.path.file_name().unwrap().to_str().unwrap();
            if self.filters.iter().any(|f| f.denied(file_name, case.line)) {
                continue;
            }
            if self.filters.iter().filter(|f| !f.negative).count() != 0
                && !self.filters.iter().any(|f| f.allowed(file_name, case.line))
            {
                continue;
            }
            ran_count += 1;
            match case.type_ {
                CaseType::Infer(expected) => {
                    let actual: HashSet<_> = script
                        .infer_definition(
                            &|name| {
                                name.name().to_owned()
                                    + (if name.kind() == ValueKind::Object {
                                        "()"
                                    } else {
                                        ""
                                    })
                            },
                            Position::LineColumn(case.line, case.column),
                        )
                        .collect();
                    assert_eq!(actual, expected);
                }
                CaseType::Complete(expected) => {
                    ran_count -= 1;
                    // TODO implement complete tests
                }
            }
        }
        (ran_count, full_count)
    }

    fn find_test_cases(&self) -> Vec<TestCase> {
        let mut cases = vec![];
        let lines: Vec<_> = self.code.split('\n').collect();
        for (line_nr, line) in lines.iter().enumerate() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("#?") {
                let mut names: Vec<_> = trimmed[2..].trim_start().split(" ").collect();
                let rest;
                let column = {
                    if let Ok(c) = names[0].parse() {
                        names.remove(0);
                        rest = names.join(" ");
                        c
                    } else {
                        rest = trimmed[2..].trim().to_owned();
                        lines[line_nr + 1].len()
                    }
                };
                let type_ = if trimmed.ends_with("]") {
                    CaseType::Complete(
                        rest[1..rest.len() - 1]
                            .split(",")
                            .map(|quoted| {
                                let quoted = quoted.trim();
                                // Strip quotes
                                quoted[1..quoted.len() - 1].to_owned()
                            })
                            .collect(),
                    )
                } else {
                    CaseType::Infer(names.iter().cloned().map(|x| x.to_owned()).collect())
                };
                cases.push(TestCase {
                    // We need to add one, because we're evaluating the next line
                    line: line_nr + 1,
                    column,
                    type_,
                });
            }
        }
        cases
    }
}

impl std::fmt::Debug for TestFile<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("TestFile")
            .field("path", &self.path)
            .finish()
    }
}
