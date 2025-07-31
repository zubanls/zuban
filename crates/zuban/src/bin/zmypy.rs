use std::process::ExitCode;

use clap::Parser as _;

fn main() -> ExitCode {
    let parsed = zmypy::Cli::parse();
    if let Err(err) = logging_config::setup_logging_without_printing_errors_by_default() {
        panic!("{err}")
    }
    zmypy::run(parsed)
}
