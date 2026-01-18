use std::process::ExitCode;

use clap::{Parser, Subcommand};

/// A fast type checker and language server for Python, written in Rust
#[derive(Parser)]
#[command(name = "zuban")]
#[command(version, about)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Checks a file or project for type errors
    Check(#[command(flatten)] cli_args::Cli),
    /// Type checks files like you would do when calling `mypy`
    Mypy(#[command(flatten)] cli_args::MypyCli),
    /// Starts an LSP server
    Server {},
}

fn main() -> ExitCode {
    let run_check = |zmypy_config: cli_args::Cli| {
        if let Err(err) = logging_config::setup_logging_without_printing_errors_by_default() {
            panic!("{err}")
        };
        zmypy::run(zmypy_config)
    };
    match Cli::parse().command {
        Commands::Mypy(mypy_options) => run_check(cli_args::Cli::new_mypy_compatible(mypy_options)),
        Commands::Check(zmypy_config) => run_check(zmypy_config),
        Commands::Server {} => match run_server() {
            Ok(()) => ExitCode::from(0),
            Err(err) => {
                eprintln!("{err}");
                ExitCode::from(1)
            }
        },
    }
}

fn run_server() -> anyhow::Result<()> {
    logging_config::setup_logging(None)?;

    // Logging to stderr.
    tracing::info!("Starting the Zuban Language Server");

    event_loop_thread(move || {
        zubanls::run_server()?;
        Ok(())
    })?;

    // Shut down gracefully.
    tracing::info!("Successfully shutting down server");
    Ok(())
}

/// The event loop thread is actually a secondary thread that we spawn from the
/// _actual_ main thread. This secondary thread has a larger stack size
/// than some OS defaults (Windows, for example) and is also designated as
/// high-priority.
pub(crate) fn event_loop_thread(
    func: impl FnOnce() -> anyhow::Result<()> + Send + 'static,
) -> anyhow::Result<()> {
    // Override OS defaults to avoid stack overflows on platforms with low stack size defaults.
    const MAIN_THREAD_STACK_SIZE: usize = 2 * 1024 * 1024;
    const MAIN_THREAD_NAME: &str = "zubanls:main";
    let handle = std::thread::Builder::new()
        .name(MAIN_THREAD_NAME.into())
        .stack_size(MAIN_THREAD_STACK_SIZE)
        .spawn(func)?;

    handle
        .join()
        .map_err(|e| anyhow::anyhow!("Error while joining the thread: {e:?}"))?
}
