use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;
use std::time::Instant;

use clap::Parser;

#[derive(Parser)]
#[command(version, about)]
pub struct Cli {
    /// Specify a project to only run this one.
    #[arg(short, long)]
    project: Option<String>,
    /// These args are passed to zmypy. You can use -- before --some-arg
    #[arg(num_args = 0..)]
    mypy_args: Vec<String>,
    /// Skips all projects before this project (sorted alphabetically)
    #[arg(long)]
    start_at: Option<String>,
    /// Ignore this specific project
    #[arg(long)]
    ignore: Option<String>,
}

fn main() -> ExitCode {
    if let Err(err) = logging_config::setup_logging(None) {
        panic!("{err}")
    }
    let primer_projects_dir = env::var("HOME").unwrap() + "/tmp/mypy_primer/projects";
    let cli = Cli::parse();
    let mut projects = vec![];
    if let Some(project) = cli.project {
        if cli.start_at.is_some() {
            panic!("It is not possible to use --start-at and a specific project together");
        }
        projects.push(project);
    } else {
        let entries = fs::read_dir(&primer_projects_dir).unwrap();
        projects = entries
            .filter_map(|entry| {
                let entry = entry.ok()?;
                let name = entry.file_name().into_string().ok()?;
                (!name.ends_with("_venv")).then_some(name)
            })
            .collect();
        projects.sort();
        if let Some(name) = cli.start_at {
            let Some(pos) = projects.iter().position(|p| *p == name) else {
                panic!("Did not found {name} in the project list");
            };
            projects.drain(..pos);
        }
    }
    if let Some(ignore) = cli.ignore {
        projects.retain(|p| p != &ignore);
    }

    let start = Instant::now();
    let mut file_count = 0;
    let mut issue_count = 0;

    for dir in projects {
        println!("Start checking {dir}");
        let project_start = Instant::now();

        let venv = Path::new(&primer_projects_dir).join(format!("_{}_venv", dir));
        let executable = venv
            .join("bin/python")
            .into_os_string()
            .into_string()
            .unwrap();
        let pth = Path::new(&primer_projects_dir)
            .join(&dir)
            .into_os_string()
            .into_string()
            .unwrap();
        env::set_current_dir(&pth).expect("Failed to change directory");

        let mut v = vec!["".into(), "--python-executable".into(), executable];
        v.extend_from_slice(&cli.mypy_args);
        let cli = cli_args::Cli::parse_from(v);
        let result = zmypy::with_diagnostics_from_cli(
            cli,
            pth,
            Some(test_utils::typeshed_path()),
            |mut diagnostics, config| {
                diagnostics.sort_issues_by_kind();
                for diagnostic in diagnostics.issues.iter() {
                    println!("{}", diagnostic.as_string(config))
                }
                file_count += diagnostics.checked_files;
                issue_count += diagnostics.issues.len();
                println!("{}", diagnostics.summary());
                if !diagnostics.issues.is_empty() {
                    println!(
                        "Mypy generated diagnostics, which leads to an error code that was ignored"
                    );
                }
            },
        );
        if let Err(err) = result {
            eprintln!("Checking diagnostics caused error: {err}");
        }

        println!(
            "Time taken for project {dir}: {:?}",
            project_start.elapsed()
        );
    }
    println!(
        "Full time taken: {:?} for {} files and found {} issues",
        start.elapsed(),
        file_count,
        issue_count
    );

    ExitCode::SUCCESS
}
