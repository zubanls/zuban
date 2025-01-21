use std::process::ExitCode;

use clap::Parser as _;

fn main() -> ExitCode {
    zmypy::run(zmypy::Cli::parse())
}
