use std::{cell::RefCell, panic::PanicHookInfo};

type PanicHook = Box<dyn Fn(&PanicHookInfo<'_>) + 'static>;

pub struct RestorePanicHook();

impl Drop for RestorePanicHook {
    fn drop(&mut self) {
        with_hook(|x| *x = None)
    }
}

pub fn enter(new_hook: PanicHook) -> RestorePanicHook {
    // Remove the previous hook and set a new one for now
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |panic_info| {
        with_hook(|maybe_custom_hook| match maybe_custom_hook {
            Some(new_hook) => new_hook(panic_info),
            None => default_hook(panic_info),
        })
    }));
    with_hook(move |maybe_custom_hook| {
        *maybe_custom_hook = Some(new_hook);
    });
    RestorePanicHook()
}

fn with_hook(f: impl FnOnce(&mut Option<PanicHook>)) {
    thread_local! {
        static CTX: RefCell<Option<PanicHook>> = const { RefCell::new(None) };
    }
    CTX.with(|ctx| f(&mut ctx.borrow_mut()));
}
