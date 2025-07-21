use clap::{Parser, Subcommand};
use shlex::Shlex;
use vfs::NormalizedPath;
use zuban_python::{GotoGoal, InputPosition, Name as _, Project};

use crate::base_path_join;

#[derive(Parser, Debug)]
#[command()]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
    #[arg(long)]
    pub column: Option<usize>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    Complete(CompleteArgs),
    Goto(GotoArgs),
    Infer(InferArgs),
}

#[derive(Parser, Debug)]
pub struct CompleteArgs {
    #[arg(long)]
    pub contains_subset: Vec<String>,
}

#[derive(Parser, Debug)]
pub struct GotoArgs {
    #[arg(long)]
    pub prefer_stubs: bool,
    #[arg(long)]
    pub follow_imports: bool,
}

#[derive(Parser, Debug)]
pub struct InferArgs {
    #[arg(long)]
    pub prefer_stubs: bool,
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
            let position = InputPosition::CodePoints {
                line: line_nr + 1,
                column: cli.column.unwrap_or_else(|| {
                    // The position on which we complete is the end of the next line
                    iterator
                        .peek()
                        .expect("Expect a line after #?")
                        .1
                        .chars()
                        .count()
                }),
            };
            let (kind, out) = match cli.command {
                Commands::Complete(complete_args) => (
                    "complete",
                    document.complete(position, |name| {
                        // TODO
                        name.label().to_owned()
                    }),
                ),
                Commands::Goto(goto_args) => {
                    let goal = match goto_args.prefer_stubs {
                        false => GotoGoal::PreferNonStubs,
                        true => GotoGoal::PreferStubs,
                    };
                    (
                        "goto",
                        document.goto(position, goal, goto_args.follow_imports, |name| {
                            let start = name.name_range().0;
                            format!(
                                "{}:{}:{}",
                                name.relative_path(base_path),
                                start.line_one_based(),
                                start.code_points_column()
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
                        document.infer_definition(position, goal, |name| {
                            let start = name.name_range().0;
                            format!(
                                "{}:{}:{}",
                                name.relative_path(base_path),
                                start.line_one_based(),
                                start.code_points_column()
                            )
                        }),
                    )
                }
            };
            output.push(match out {
                Ok(out) => {
                    let result = if kind == "complete" {
                        format!("[{}]", out.join(", "))
                    } else {
                        out.join("; ")
                    };
                    format!("{path}:{}:{kind} -> {}", line_nr + 2, result)
                }
                Err(err) => format!("{path}:{}:{kind} -> error: {err}", line_nr + 2),
            });
        }
    }
}
