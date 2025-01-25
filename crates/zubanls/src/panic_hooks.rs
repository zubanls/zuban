use std::{cell::Cell, panic::PanicHookInfo};

type PanicHook = Box<dyn Fn(&PanicHookInfo<'_>) + 'static>;

thread_local! {
    static HOOK: Cell<Option<PanicHook>> = const { Cell::new(None) };
}

pub struct RestorePanicHook();

impl Drop for RestorePanicHook {
    fn drop(&mut self) {
        HOOK.with(|cell| cell.take());
    }
}

pub fn enter(new_hook: PanicHook) -> RestorePanicHook {
    // Remove the previous hook and set a new one for now
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |panic_info| {
        HOOK.with(|cell| match cell.take() {
            Some(new_hook) => new_hook(panic_info),
            None => default_hook(panic_info),
        })
    }));
    HOOK.with(move |cell| {
        cell.set(Some(new_hook));
    });
    RestorePanicHook()
}
