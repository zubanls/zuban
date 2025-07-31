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
    Documentation(DocumentationArgs),
    References(ReferencesArgs),
    Rename(RenameArgs),
}

#[derive(Parser, Debug)]
pub struct CompleteArgs {
    #[arg(long)]
    pub filter: Option<Vec<String>>,
    #[arg(long)]
    pub show_kind: bool,
}

#[derive(Parser, Debug)]
pub struct GotoArgs {
    #[arg(long)]
    pub follow_imports: bool,
    #[command(flatten)]
    pub common_args: CommonGotoInferArgs,
}

#[derive(Parser, Debug)]
pub struct CommonGotoInferArgs {
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
pub struct InferArgs {
    #[command(flatten)]
    pub common_args: CommonGotoInferArgs,
}

#[derive(Parser, Debug)]
pub struct DocumentationArgs {
    #[arg(long)]
    only_docstrings: bool,
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

impl CommonGotoInferArgs {
    fn goto_goal(&self) -> GotoGoal {
        match self.prefer_stubs {
            false => GotoGoal::PreferNonStubs,
            true => GotoGoal::PreferStubs,
        }
    }
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
                    (None, None, None, None) => InputPosition::Utf8Bytes {
                        line,
                        column: iterator
                            .peek()
                            .expect("Expect a line after #?")
                            .1
                            .trim_end_matches('\r')
                            .len(),
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
            let check_infer_or_goto = |name: &Name, common_args: &CommonGotoInferArgs| {
                let start = name.name_range().0;
                if let Some(expected_doc) = &common_args.doc_contains {
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
                } else if let Some(expected_doc) = &common_args.doc_is {
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
                } else if common_args.no_positions {
                    format!(
                        "{}:{}",
                        clean_path(name.path_relative_to_workspace()),
                        name.qualified_name(),
                    )
                } else {
                    format!(
                        "{}:{}:{}:{}",
                        clean_path(name.path_relative_to_workspace()),
                        start.line_one_based(),
                        start.code_points_column(),
                        name.qualified_name(),
                    )
                }
            };
            let test_on_line_nr = line_nr + 2;
            let (kind, out) = match cli.command {
                Commands::Complete(complete_args) => {
                    let mut result = document.complete(position, true, |_, name| {
                        if complete_args.show_kind {
                            format!("{}:{:?}", name.label(), name.kind())
                        } else {
                            name.label().to_owned()
                        }
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
                    let goal = goto_args.common_args.goto_goal();
                    (
                        "goto",
                        document.goto(position, goal, goto_args.follow_imports, |name| {
                            check_infer_or_goto(&name, &goto_args.common_args)
                        }),
                    )
                }
                Commands::Infer(infer_args) => {
                    let goal = infer_args.common_args.goto_goal();
                    (
                        "infer",
                        document.infer_definition(position, goal, |vn| {
                            check_infer_or_goto(&vn.name, &infer_args.common_args)
                        }),
                    )
                }
                Commands::Documentation(d) => (
                    "documentation",
                    document
                        .documentation(position, d.only_docstrings)
                        .map(|result| {
                            vec![match result {
                                Some(result) => format!("{:?}", result.documentation),
                                None => "No docs found".to_string(),
                            }]
                        }),
                ),
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
                                        clean_path(name.path_relative_to_workspace()),
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
                                        std::iter::once(format!(
                                            "{}:",
                                            cleanup_rename_uri(c.path.as_uri())
                                        ))
                                        .chain(
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
                                        format!(
                                            "Rename: {} -> {}",
                                            cleanup_rename_uri(r.from_uri()),
                                            cleanup_rename_uri(r.to_uri())
                                        )
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

fn clean_path(p: String) -> String {
    if cfg!(windows) {
        p.replace('\\', "/")
    } else {
        p
    }
}

fn cleanup_rename_uri(u: String) -> String {
    u.replace("C://mypylike", "mypylike")
}
