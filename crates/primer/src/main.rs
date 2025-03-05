use std::env;
use std::fs;
use std::path::Path;
use std::process::ExitCode;
use std::time::Instant;

use clap::Parser;

#[derive(Parser)]
#[command(version, about)]
pub struct Cli {
    #[arg(num_args = 0..)]
    projects: Vec<String>,
}

fn main() -> ExitCode {
    let primer_projects_dir = env::var("HOME").unwrap() + "/tmp/mypy_primer/projects";
    let cli = Cli::parse();
    let mut projects = cli.projects;
    if projects.is_empty() {
        let entries = fs::read_dir(&primer_projects_dir).unwrap();
        projects = entries
            .filter_map(|entry| {
                let entry = entry.ok()?;
                let name = entry.file_name().into_string().ok()?;
                (!name.ends_with("_venv")).then_some(name)
            })
            .collect();
        projects.sort();
    }

    let start = Instant::now();

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

        let cli = zmypy::Cli::parse_from(&["", "--python-executable", &executable]);
        let code = zmypy::run_with_cli(cli, pth, Some(test_utils::typeshed_path()));
        if code == ExitCode::FAILURE {
            println!("Mypy generated diagnostics, which leads to an error code that was ignored");
        }

        println!(
            "Time taken for project {dir}: {:?}",
            project_start.elapsed()
        );
    }
    println!("Full time taken: {:?}", start.elapsed());

    ExitCode::SUCCESS
}
