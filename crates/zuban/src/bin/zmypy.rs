use std::process::ExitCode;

use clap::Parser as _;

fn main() -> ExitCode {
    let parsed = zmypy::Cli::parse();
    if let Err(err) = logging_config::setup_logging(None) {
        panic!("{err}")
    }
    zmypy::run(parsed)
}
