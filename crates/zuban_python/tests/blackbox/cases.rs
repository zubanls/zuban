use std::path::Path;

use utils::FastHashSet;
use vfs::PathWithScheme;
use zuban_python::{Document, GotoGoal, InputPosition, Project, ReferencesGoal, SymbolKind};

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
    Infer {
        expected: FastHashSet<String>,
        goal: GotoGoal,
    },
    Goto {
        expected: Vec<String>,
        goal: GotoGoal,
        follow_imports: bool,
    },
    Complete {
        expected: Vec<String>,
        contains_subset: bool,
        contains_not: Vec<String>,
    },
    References {
        expected: FastHashSet<(Option<String>, usize, usize)>,
    },
}

enum DocumentKeeper<'project> {
    Uninitialized(&'project mut Project, PathWithScheme),
    Document(Document<'project>),
    InBetweenStates,
}

impl<'project> DocumentKeeper<'project> {
    fn get(&mut self) -> &Document<'_> {
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
        let file_name = self.path.file_name().unwrap().to_str().unwrap();
        for case in cases {
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
                CaseType::Infer { expected, goal } => {
                    let actual: FastHashSet<_> = document
                        .get()
                        .infer_definition(position, goal, |vn| {
                            let mut n = if *vn.name.file_path() == *path {
                                vn.name.name().to_owned()
                            } else {
                                let mut s = vn.name.qualified_name();
                                if let Some(rest) = s.strip_prefix("builtins.") {
                                    s = rest.to_string();
                                }
                                s
                            };
                            if vn.is_instance() {
                                n.push_str("()");
                            }
                            n
                        })
                        .unwrap()
                        .into_iter()
                        .collect();
                    if actual != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
                CaseType::Goto {
                    expected,
                    goal,
                    follow_imports,
                } => {
                    let actual = document
                        .get()
                        .goto(position, goal, follow_imports, |name| {
                            if name.kind() == SymbolKind::Module {
                                format!("module {}", name.qualified_name())
                            } else {
                                name.target_range_code()
                                    .split('\n')
                                    .next()
                                    .unwrap()
                                    .trim()
                                    .to_owned()
                            }
                        })
                        .unwrap();
                    if actual != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
                CaseType::References { expected } => {
                    let actual = document
                        .get()
                        .references(
                            position,
                            ReferencesGoal::OnlyTypeCheckedWorkspaces,
                            true,
                            |name| {
                                let identifier = if *name.file_path() == *path {
                                    None
                                } else {
                                    let s = name.qualified_name_of_file();
                                    Some(if name.in_stub() {
                                        format!("stub:{s}")
                                    } else {
                                        s
                                    })
                                };
                                let start = name.name_range().0;
                                (
                                    identifier,
                                    start.line_one_based(),
                                    start.code_points_column(),
                                )
                            },
                        )
                        .unwrap();
                    let actual_len = actual.len();
                    let actual_set: FastHashSet<_> = actual.iter().cloned().collect();
                    if actual_set != expected {
                        errors.push(format!(
                            "{file_name}: Line #{} {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                    if actual_len != expected.len() {
                        errors.push(format!(
                            "{file_name}: Line #{} Length mismatch {expected:?} != {actual:?}",
                            case.line,
                        ));
                    }
                }
                CaseType::Complete {
                    expected,
                    contains_subset,
                    contains_not,
                } => {
                    let actual = document
                        .get()
                        .complete(position, true, |_, name| name.label().to_owned())
                        .unwrap();
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
                        lines[line_nr + 1].trim_end_matches('\r').len()
                    }
                };
                let mut contains_subset = false;
                let mut follow_imports = false;
                let mut goal = GotoGoal::PreferNonStubs;
                let mut contains_not = vec![];
                loop {
                    match names.first() {
                        Some(&"--add-lines") => {
                            names.remove(0);
                            line_nr += names.remove(1).parse::<usize>().unwrap();
                        }
                        Some(&"--contains-subset") => {
                            assert_eq!(kind, TestKind::Complete);
                            names.remove(0);
                            contains_subset = true;
                        }
                        Some(&"--contains-not") => {
                            assert_eq!(kind, TestKind::Complete);
                            names.remove(0);
                            contains_subset = true;
                            contains_not.push(names.remove(0).to_string());
                        }
                        Some(&"--follow-imports") => {
                            assert_eq!(kind, TestKind::Goto);
                            names.remove(0);
                            follow_imports = true;
                        }
                        Some(&"--prefer-stubs") => {
                            assert!(matches!(kind, TestKind::Goto | TestKind::Infer));
                            names.remove(0);
                            goal = GotoGoal::PreferStubs;
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
                    TestKind::Infer => CaseType::Infer {
                        expected: names.iter().cloned().map(|x| x.to_owned()).collect(),
                        goal,
                    },
                    TestKind::Goto => CaseType::Goto {
                        expected: unpack_list(),
                        goal,
                        follow_imports,
                    },
                    TestKind::Complete => CaseType::Complete {
                        expected: unpack_list(),
                        contains_subset,
                        contains_not,
                    },
                    TestKind::References => CaseType::References {
                        expected: unpack_references_tuple(line_nr, &names.join(" ")),
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

fn unpack_references_tuple(
    line_nr: usize,
    mut s: &str,
) -> FastHashSet<(Option<String>, usize, usize)> {
    let mut tuples = FastHashSet::default();
    while !s.is_empty() {
        s = s.strip_prefix('(').unwrap();
        let mut in_tuple;
        (in_tuple, s) = s.split_once(')').unwrap();
        let mut identifier = None;
        if let Some(after_opening_string) = in_tuple.strip_prefix('\'') {
            let in_string;
            (in_string, in_tuple) = after_opening_string.split_once('\'').unwrap();
            in_tuple = in_tuple.strip_prefix(',').unwrap();
            identifier = Some(in_string.to_string())
        }
        let (line, column) = in_tuple.split_once(',').unwrap();
        let line = if identifier.is_some() {
            line.trim().parse::<usize>().unwrap()
        } else {
            let line_diff = line.trim().parse::<isize>().unwrap();
            (line_nr as isize + 2 + line_diff) as usize
        };
        let column = column.trim().parse().unwrap();
        assert!(tuples.insert((identifier, line, column)));
        s = s.trim_start_matches(',');
        s = s.trim_start();
    }
    tuples
}

#[derive(Debug, PartialEq)]
enum TestKind {
    Infer,
    Goto,
    Complete,
    References,
}

fn find_test_kind(line: &str) -> Option<(TestKind, &str)> {
    let trimmed = line.trim_start().trim_end_matches('\r');
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
    } else if let Some(stripped) = trimmed.strip_prefix("#<") {
        (TestKind::References, stripped)
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
