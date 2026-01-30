mod helpers;
mod ls;
mod stubs;

use once_cell::sync::Lazy;

pub use ls::LS;

static PANIC_HOOK: Lazy<()> = Lazy::new(|| {
    console_error_panic_hook::set_once();
});
