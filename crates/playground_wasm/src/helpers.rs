use std::any::Any;

use vfs::InMemoryFs;

use crate::stubs::BUNDLED_STUBS;

pub fn prepare_filesystem() -> InMemoryFs {
    let fs = InMemoryFs::new();
    for (path, contents) in BUNDLED_STUBS {
        fs.set_file(path, contents.to_string());
    }
    fs
}

pub fn panic_payload_to_string(payload: Box<dyn Any + Send>) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_string())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "panic".to_string())
}
