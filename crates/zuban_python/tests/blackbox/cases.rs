#![allow(dead_code)]
use std::{collections::HashSet, path::Path};

use vfs::PathWithScheme;
use zuban_python::{InputPosition, Name};

use crate::Filter;

pub struct TestFile<'a> {
    pub path: &'a Path,
    pub code: Box<str>,
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
    Goto(Vec<String>),
    Complete(Vec<String>),
}

impl TestFile<'_> {
    pub fn test(&self, project: &mut zuban_python::Project) -> (usize, usize, usize) {
        let path = project
            .vfs_handler()
            .normalize_uncheck_abs_path(self.path.to_str().unwrap());
        let document = project
            .document(&PathWithScheme::with_file_scheme(path.clone()))
            .unwrap();
        let cases = self.find_test_cases();
        let full_count = cases.len();
        let mut ran_count = 0;
        let mut errors = vec![];
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
            let position = InputPosition::Utf8Bytes {
                line: case.line,
                column: case.column,
            };
            match case.type_ {
                CaseType::Infer(expected) => {
                    let actual: HashSet<_> = document
                        .infer_type_definition(position, |name| {
                            let mut n = if *name.file_path() == *path {
                                name.name().to_owned()
                            } else {
                                let mut s = name.qualified_name();
                                if let Some(rest) = s.strip_prefix("builtins.") {
                                    s = rest.to_string();
                                }
                                s
                            };
                            if name.is_instance() {
                                n.push_str("()");
                            }
                            n
                        })
                        .collect();
                    if actual != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
                CaseType::Goto(expected) => {
                    let actual: Vec<_> = document.goto(position, false, |name| {
                        name.target_range_code()
                            .split('\n')
                            .next()
                            .unwrap()
                            .trim()
                            .to_owned()
                    });
                    if actual != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
                CaseType::Complete(expected) => {
                    let actual: Vec<_> =
                        document.complete(position, |name| name.label().to_owned());
                    if actual != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
            }
        }
        if !errors.is_empty() {
            for error in &errors {
                println!("{error}");
            }
            /*
            let file_name = self.path.file_name().unwrap().to_str().unwrap();
            println!(
                "{file_name} Ran {ran_count} tests with {} errors",
                errors.len()
            );
            */
        }
        (ran_count, full_count, errors.len())
    }

    fn find_test_cases(&self) -> Vec<TestCase> {
        let mut cases = vec![];
        let lines: Vec<_> = self.code.split('\n').collect();
        for (line_nr, line) in lines.iter().enumerate() {
            if let Some((kind, stripped)) = find_test_kind(line) {
                let mut names: Vec<_> = stripped.trim_start().split(' ').collect();
                let rest;
                let column = {
                    if let Ok(c) = names[0].parse() {
                        names.remove(0);
                        rest = names.join(" ");
                        c
                    } else {
                        rest = stripped.trim().to_owned();
                        lines[line_nr + 1].len()
                    }
                };
                if names.last().unwrap().is_empty() {
                    // Splittling leaves an empty string if nothing is provided
                    names.pop();
                }
                let unpack_list = || {
                    rest[1..rest.len() - 1]
                        .split(',')
                        .filter(|x| !x.is_empty())
                        .map(|quoted| {
                            let quoted = quoted.trim();
                            // Strip quotes
                            quoted[1..quoted.len() - 1].to_owned()
                        })
                        .collect()
                };
                let type_ = match kind {
                    TestKind::Infer => {
                        CaseType::Infer(names.iter().cloned().map(|x| x.to_owned()).collect())
                    }
                    TestKind::Goto => CaseType::Goto(unpack_list()),
                    TestKind::Complete => CaseType::Complete(unpack_list()),
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

enum TestKind {
    Infer,
    Goto,
    Complete,
}

fn find_test_kind(line: &str) -> Option<(TestKind, &str)> {
    let trimmed = line.trim_start();
    Some(if let Some(stripped) = trimmed.strip_prefix("#?") {
        (
            if trimmed.ends_with(']') {
                TestKind::Complete
            } else {
                TestKind::Infer
            },
            stripped,
        )
    } else if let Some(stripped) = trimmed.strip_prefix("#!") {
        (TestKind::Goto, stripped)
    } else {
        return None;
    })
}

impl std::fmt::Debug for TestFile<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("TestFile")
            .field("path", &self.path)
            .finish()
    }
}
