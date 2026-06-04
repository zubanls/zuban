mod capabilities;
mod client_config;
mod notebooks;
mod notification_handlers;
mod panic_hooks;
mod request_handlers;
mod semantic_tokens;
mod server;

pub use crate::server::{
    GLOBAL_NOTIFY_EVENT_COUNTER, run_server, run_server_with_custom_connection,
};

use clap::Parser;

#[derive(Parser, Clone, Default, Debug)]
pub struct Cli {
    /// Specifies the path for a python executable (for example a virtual env)
    #[arg(long)]
    python_executable: Option<String>,
}
