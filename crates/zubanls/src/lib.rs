mod capabilities;
mod notebooks;
#[cfg(not(target_arch = "wasm32"))]
mod panic_hooks;
mod semantic_tokens;
mod server;
#[cfg(target_arch = "wasm32")]
mod wasm;

mod notification_handlers;
mod request_handlers;

#[cfg(not(target_arch = "wasm32"))]
pub use crate::server::{
    GLOBAL_NOTIFY_EVENT_COUNTER, run_server, run_server_with_custom_connection,
};

#[cfg(target_arch = "wasm32")]
pub use crate::wasm::{ZubanLS, start};
