use clap::{Parser, Subcommand};
use shlex::Shlex;
use vfs::NormalizedPath;
use zuban_python::{GotoGoal, InputPosition, Name, Project, ReferencesGoal};

use crate::base_path_join;

#[derive(Parser, Debug)]
#[command()]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
    #[arg(long)]
    pub codepoint_column: Option<usize>,
    #[arg(long)]
    pub utf8_bytes_column: Option<usize>,
    #[arg(long)]
    pub utf16_code_units_column: Option<usize>,
    #[arg(long)]
    pub nth_utf8_byte: Option<usize>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    Complete(CompleteArgs),
    Goto(GotoArgs),
    Infer(InferArgs),
    References(ReferencesArgs),
    Rename(RenameArgs),
}

#[derive(Parser, Debug)]
pub struct CompleteArgs {
    #[arg(long)]
    pub filter: Option<Vec<String>>,
}

#[derive(Parser, Debug)]
pub struct GotoArgs {
    #[arg(long)]
    pub prefer_stubs: bool,
    #[arg(long)]
    pub follow_imports: bool,
    #[arg(long)]
    pub no_positions: bool,
    #[arg(long)]
    pub doc_contains: Option<String>,
    #[arg(long)]
    pub doc_is: Option<String>,
}

#[derive(Parser, Debug)]
pub struct InferArgs {
    #[arg(long)]
    pub prefer_stubs: bool,
    #[arg(long)]
    pub no_positions: bool,
    #[arg(long)]
    pub doc_contains: Option<String>,
    #[arg(long)]
    pub doc_is: Option<String>,
}

#[derive(Parser, Debug)]
pub struct ReferencesArgs {
    #[arg(long)]
    only_check_file: bool,
    #[arg(long)]
    no_include_declarations: bool,
}

#[derive(Parser, Debug)]
pub struct RenameArgs {
    #[arg()]
    pub new_name: String,
}

pub(crate) fn find_and_check_ide_tests(
    project: &mut Project,
    base_path: &NormalizedPath,
    path: &str,
    code: &str,
    output: &mut Vec<String>,
) {
    let mut iterator = code.split('\n').enumerate().peekable();
    while let Some((line_nr, line)) = iterator.next() {
        let rest = line.trim();
        if let Some(after_comment) = rest.strip_prefix("#?") {
            let cli =
                Cli::parse_from(std::iter::once("".to_string()).chain(Shlex::new(after_comment)));
            let p = base_path_join(project.vfs_handler(), path);
            let document = project.document(&p).unwrap();
            let position = {
                let line = line_nr + 1;
                match (
                    cli.codepoint_column,
                    cli.utf8_bytes_column,
                    cli.utf16_code_units_column,
                    cli.nth_utf8_byte,
                ) {
                    // The position on which we complete is the end of the next line
                    (None, None, None, None) => InputPosition::CodePoints {
                        line,
                        column: iterator
                            .peek()
                            .expect("Expect a line after #?")
                            .1
                            .chars()
                            .count(),
                    },
                    (Some(column), None, None, None) => InputPosition::CodePoints { line, column },
                    (None, Some(column), None, None) => InputPosition::Utf8Bytes { line, column },
                    (None, None, Some(column), None) => {
                        InputPosition::Utf16CodeUnits { line, column }
                    }
                    (None, None, None, Some(nth_byte)) => InputPosition::NthUTF8Byte(nth_byte),
                    _ => panic!("The test should not ever pass multiple position informations"),
                }
            };
            let check_infer_or_goto = |name: &Name,
                                       doc_contains: &Option<String>,
                                       doc_is: &Option<String>,
                                       no_positions: bool| {
                let start = name.name_range().0;
                if let Some(expected_doc) = doc_contains {
                    let actual = name.documentation();
                    if actual.contains(expected_doc) {
                        format!("Doc for {} matched", name.qualified_name())
                    } else {
                        format!(
                            "Doc for {} did not match: {:?} does not contain {:?}",
                            name.qualified_name(),
                            actual,
                            expected_doc
                        )
                    }
                } else if let Some(expected_doc) = doc_is {
                    let actual = name.documentation();
                    if &*actual == expected_doc {
                        format!("Doc for {} matched", name.qualified_name())
                    } else {
                        format!(
                            "Doc for {} did not match: {:?} does not contain {:?}",
                            name.qualified_name(),
                            actual,
                            expected_doc
                        )
                    }
                } else if no_positions {
                    format!(
                        "{}:{}",
                        name.path_relative_to_workspace(),
                        name.qualified_name(),
                    )
                } else {
                    format!(
                        "{}:{}:{}:{}",
                        name.path_relative_to_workspace(),
                        start.line_one_based(),
                        start.code_points_column(),
                        name.qualified_name(),
                    )
                }
            };
            let test_on_line_nr = line_nr + 2;
            let (kind, out) = match cli.command {
                Commands::Complete(complete_args) => {
                    let mut result = document.complete(position, |name| {
                        // TODO
                        name.label().to_owned()
                    });
                    if let Some(filter) = complete_args.filter {
                        if let Ok(r) = result {
                            result =
                                Ok(r.into_iter().filter(|item| filter.contains(item)).collect());
                        }
                    }
                    ("complete", result)
                }
                Commands::Goto(goto_args) => {
                    let goal = match goto_args.prefer_stubs {
                        false => GotoGoal::PreferNonStubs,
                        true => GotoGoal::PreferStubs,
                    };
                    (
                        "goto",
                        document.goto(position, goal, goto_args.follow_imports, |name| {
                            check_infer_or_goto(
                                &name,
                                &goto_args.doc_contains,
                                &goto_args.doc_is,
                                goto_args.no_positions,
                            )
                        }),
                    )
                }
                Commands::Infer(infer_args) => {
                    let goal = match infer_args.prefer_stubs {
                        false => GotoGoal::PreferNonStubs,
                        true => GotoGoal::PreferStubs,
                    };
                    (
                        "infer",
                        document.infer_definition(position, goal, |vn| {
                            check_infer_or_goto(
                                &vn.name,
                                &infer_args.doc_contains,
                                &infer_args.doc_is,
                                infer_args.no_positions,
                            )
                        }),
                    )
                }
                Commands::References(references) => {
                    let goal = match references.only_check_file {
                        true => ReferencesGoal::OnlyCurrentFile,
                        false => ReferencesGoal::OnlyTypeCheckedWorkspaces,
                    };
                    (
                        "references",
                        document.references(
                            position,
                            goal,
                            !references.no_include_declarations,
                            |name| {
                                let start = name.name_range().0;
                                if name.file_path() == base_path {
                                    format!(
                                        "{}:{}",
                                        start.line_one_based(),
                                        start.code_points_column()
                                    )
                                } else {
                                    format!(
                                        "{}:{}:{}",
                                        name.path_relative_to_workspace(),
                                        start.line_one_based(),
                                        start.code_points_column(),
                                    )
                                }
                            },
                        ),
                    )
                }
                Commands::Rename(rename) => {
                    match document.references_for_rename(position, &rename.new_name) {
                        Ok(result) => {
                            let results = std::iter::once(format!(
                                "{} -> {}",
                                result.old_name, result.new_name
                            ))
                            .chain(
                                result
                                    .changes
                                    .iter()
                                    .map(|c| {
                                        std::iter::once(format!("{}:", c.path.as_uri())).chain(
                                            c.ranges.iter().map(|(start, end)| {
                                                format!(
                                                    " - ({}, {}) -> ({}, {})",
                                                    start.line_one_based(),
                                                    start.code_points_column(),
                                                    end.line_one_based(),
                                                    end.code_points_column(),
                                                )
                                            }),
                                        )
                                    })
                                    .flatten()
                                    .chain(result.renames().map(|r| {
                                        format!("Rename: {} -> {}", r.from_uri(), r.to_uri())
                                    })),
                            );
                            output.extend(
                                results.map(|r| format!("{path}:{test_on_line_nr}:rename: {r}")),
                            );
                            continue;
                        }
                        Err(err) => ("rename", Err(err)),
                    }
                }
            };
            output.push(match out {
                Ok(out) => {
                    let result = if kind == "complete" {
                        format!("[{}]", out.join(", "))
                    } else {
                        if out.is_empty() {
                            "()".to_string()
                        } else {
                            out.join("; ")
                        }
                    };
                    format!("{path}:{}:{kind} -> {}", test_on_line_nr, result)
                }
                Err(err) => format!("{path}:{}:{kind} -> error: {err}", test_on_line_nr),
            });
        }
    }
}
