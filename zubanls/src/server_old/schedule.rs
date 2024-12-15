use self::{
    task::{BackgroundTaskBuilder, SyncTask},
    thread::ThreadPriority,
};
use super::{client::Client, ClientSender};

use lsp_server::RequestId;
use serde::Serialize;

use crate::{
    server::client::{Notifier, Requester, Responder},
    session::Session,
};

type LocalFn<'s> = Box<dyn FnOnce(&mut Session, Notifier, &mut Requester, Responder) + 's>;

pub(in crate::server) enum Task<'s> {
    Sync(SyncTask<'s>),
}

pub(in crate::server) struct SyncTask<'s> {
    pub(super) func: LocalFn<'s>,
}

impl<'s> Task<'s> {
    /// Creates a new local task.
    pub(crate) fn local(
        func: impl FnOnce(&mut Session, Notifier, &mut Requester, Responder) + 's,
    ) -> Self {
        Self::Sync(SyncTask {
            func: Box::new(func),
        })
    }
    /// Creates a local task that immediately
    /// responds with the provided `request`.
    pub(crate) fn immediate<R>(id: RequestId, result: crate::server::Result<R>) -> Self
    where
        R: Serialize + Send + 'static,
    {
        Self::local(move |_, _, _, responder| {
            if let Err(err) = responder.respond(id, result) {
                tracing::error!("Unable to send immediate response: {err}");
            }
        })
    }

    /// Creates a local task that does nothing.
    pub(crate) fn nothing() -> Self {
        Self::local(move |_, _, _, _| {})
    }
}
