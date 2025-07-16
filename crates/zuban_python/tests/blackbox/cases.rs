use std::{collections::HashSet, path::Path};

use vfs::PathWithScheme;
use zuban_python::{Document, InputPosition, Name, Project};

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
    Complete {
        expected: Vec<String>,
        contains_subset: bool,
        contains_not: Vec<String>,
    },
}

enum DocumentKeeper<'project> {
    Uninitialized(&'project mut Project, PathWithScheme),
    Document(Document<'project>),
    InBetweenStates,
}

impl<'project> DocumentKeeper<'project> {
    fn get(&mut self) -> &Document {
        match self {
            Self::Uninitialized(..) => {
                let Self::Uninitialized(project, path_with_scheme) =
                    std::mem::replace(self, Self::InBetweenStates)
                else {
                    unreachable!()
                };
                let document: Document<'project> = (*project).document(&path_with_scheme).unwrap();
                *self = Self::Document(document);
                self.get()
            }
            Self::Document(doc) => doc,
            Self::InBetweenStates => unreachable!(),
        }
    }
}

impl TestFile<'_> {
    pub fn test(&self, project: &mut zuban_python::Project) -> (usize, usize, usize) {
        let path = project
            .vfs_handler()
            .normalize_uncheck_abs_path(self.path.to_str().unwrap());
        let path_with_scheme = PathWithScheme::with_file_scheme(path.clone());
        let mut document = DocumentKeeper::Uninitialized(project, path_with_scheme);
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
                        .get()
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
                    let actual: Vec<_> = document.get().goto(position, false, |name| {
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
                CaseType::Complete {
                    expected,
                    contains_subset,
                    contains_not,
                } => {
                    let actual: Vec<_> = document
                        .get()
                        .complete(position, |name| name.label().to_owned());
                    for should_not_be_in_there in contains_not {
                        if actual.contains(&should_not_be_in_there) {
                            errors.push(format!(
                                "{file_name}: Line #{} Expected {should_not_be_in_there:?} \
                                 to not be in {actual:?}",
                                case.line,
                            ));
                        }
                    }
                    if contains_subset {
                        for expected_item in expected {
                            if !actual.contains(&expected_item) {
                                errors.push(format!(
                                    "{file_name}: Line #{} Expected {expected_item:?} in {actual:?}",
                                    case.line,
                                ));
                            }
                        }
                    } else if actual != expected {
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
        for (mut line_nr, line) in lines.iter().enumerate() {
            if let Some((kind, stripped)) = find_test_kind(line) {
                let mut names: Vec<_> = stripped.trim_start().split(' ').collect();
                let column = {
                    if let Ok(c) = names[0].parse() {
                        names.remove(0);
                        c
                    } else {
                        lines[line_nr + 1].len()
                    }
                };
                let mut contains_subset = false;
                let mut contains_not = vec![];
                loop {
                    match names.get(0) {
                        Some(&"--add-lines") => {
                            names.remove(0);
                            line_nr += names.remove(1).parse::<usize>().unwrap();
                        }
                        Some(&"--contains-subset") => {
                            assert!(matches!(kind, TestKind::Complete));
                            names.remove(0);
                            contains_subset = true;
                        }
                        Some(&"--contains-not") => {
                            assert!(matches!(kind, TestKind::Complete));
                            names.remove(0);
                            contains_subset = true;
                            contains_not.push(names.remove(0).to_string());
                        }
                        Some(name) if name.starts_with("--") => {
                            panic!("Did not expect option {name} in {:?}:#{line_nr}", self.path)
                        }
                        _ => break,
                    }
                }

                if names.last().is_some_and(|last| last.is_empty()) {
                    // Splittling leaves an empty string if nothing is provided
                    names.pop();
                }
                let unpack_list = || {
                    let rest = names.join(" ");
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
                    TestKind::Complete => CaseType::Complete {
                        expected: unpack_list(),
                        contains_subset,
                        contains_not,
                    },
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
