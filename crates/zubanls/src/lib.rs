mod capabilities;
mod notebooks;
#[cfg(not(target_family = "wasm"))]
mod panic_hooks;
mod semantic_tokens;
mod server;
#[cfg(target_family = "wasm")]
mod wasm;

mod notification_handlers;
mod request_handlers;

#[cfg(not(target_family = "wasm"))]
pub use crate::server::{
    GLOBAL_NOTIFY_EVENT_COUNTER, run_server, run_server_with_custom_connection,
};

#[cfg(target_family = "wasm")]
pub use crate::wasm::{ZubanLS, start};
