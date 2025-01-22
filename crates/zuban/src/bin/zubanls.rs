use anyhow::anyhow;
use std::thread;

use clap::Parser;

/// A fast language server for Python, written in Rust
#[derive(Parser)]
#[command(about)]
pub struct Cli {
    // Here we will add options in the future
}

fn main() -> anyhow::Result<()> {
    let _cli = Cli::parse();
    logging_config::setup_logging(None)?;

    // Logging to stderr.
    tracing::info!("Starting ZubanLS server");

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
    let handle = thread::Builder::new()
        .name(MAIN_THREAD_NAME.into())
        .stack_size(MAIN_THREAD_STACK_SIZE)
        .spawn(func)?;

    handle
        .join()
        .map_err(|e| anyhow!("Error while joining the thread: {e:?}"))?
}
