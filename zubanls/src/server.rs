//! Scheduling, I/O, and API endpoints.

use std::thread;
// The new PanicInfoHook name requires MSRV >= 1.82
#[allow(deprecated)]
use std::panic::PanicInfo;

use anyhow::anyhow;
use crossbeam_channel::Sender;
use lsp_server::{Connection, ExtractError, Message, Request};
use lsp_types::{
    ClientCapabilities, DiagnosticOptions, DiagnosticServerCapabilities, MessageType,
    ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    Uri,
};

//use crate::session::{AllSettings, ClientSettings, Session};
//use crate::PositionEncoding;

//mod api;
//mod client;
//mod connection;
//mod schedule;

//use crate::message::try_show_message;
//pub(crate) use connection::ClientSender;

pub(crate) struct Server {
    //connection: Connection,
    client_capabilities: ClientCapabilities,
    //session: Session,
}

const SERVER_NAME: &str = "zubanls";
const DIAGNOSTIC_NAME: &str = "ZubanLS";

fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
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

impl Server {
    pub(crate) fn new() -> anyhow::Result<Self> {
        todo!()
        /*
        let client_capabilities = init_params.capabilities;
        let position_encoding = Self::find_best_position_encoding(&client_capabilities);
        let server_capabilities = Self::server_capabilities(position_encoding);


        if let Some(trace) = init_params.trace {
            crate::trace::set_trace_value(trace);
        }

        crate::message::init_messenger(connection.make_sender());

        let AllSettings {
            global_settings,
            mut workspace_settings,
        } = AllSettings::from_value(
            init_params
                .initialization_options
                .unwrap_or_else(|| serde_json::Value::Object(serde_json::Map::default())),
        );

        crate::trace::init_tracing(
            connection.make_sender(),
            global_settings
                .tracing
                .log_level
                .unwrap_or(crate::trace::LogLevel::Info),
            global_settings.tracing.log_file.as_deref(),
            init_params.client_info.as_ref(),
        );

        let mut workspace_for_url = |url: Uri| {
            let Some(workspace_settings) = workspace_settings.as_mut() else {
                return (url, ClientSettings::default());
            };
            let settings = workspace_settings.remove(&url).unwrap_or_else(|| {
                tracing::warn!("No workspace settings found for {}", url);
                ClientSettings::default()
            });
            (url, settings)
        };

        let workspaces = init_params
            .workspace_folders
            .filter(|folders| !folders.is_empty())
            .map(|folders| folders.into_iter().map(|folder| {
                workspace_for_url(folder.uri)
            }).collect())
            .or_else(|| {
                tracing::warn!("No workspace(s) were provided during initialization. Using the current working directory as a default workspace...");
                let uri = Uri::from_file_path(std::env::current_dir().ok()?).ok()?;
                Some(vec![workspace_for_url(uri)])
            })
            .ok_or_else(|| {
                anyhow::anyhow!("Failed to get the current working directory while creating a default workspace.")
            })?;

        if workspaces.len() > 1 {
            // TODO
            anyhow::bail!("Multi-root workspaces are not supported yet");
        }

        Ok(Self {
            client_capabilities,
        })
        */
    }

    pub(crate) fn run(self) -> anyhow::Result<()> {
        // The new PanicInfoHook name requires MSRV >= 1.82
        #[allow(deprecated)]
        type PanicHook = Box<dyn Fn(&PanicInfo<'_>) + 'static + Sync + Send>;
        struct RestorePanicHook {
            hook: Option<PanicHook>,
        }

        impl Drop for RestorePanicHook {
            fn drop(&mut self) {
                if let Some(hook) = self.hook.take() {
                    std::panic::set_hook(hook);
                }
            }
        }

        // Unregister any previously registered panic hook
        // The hook will be restored when this function exits.
        let _ = RestorePanicHook {
            hook: Some(std::panic::take_hook()),
        };

        // When we panic, try to notify the client.
        std::panic::set_hook(Box::new(move |panic_info| {
            /*
            use std::io::Write;

            let backtrace = std::backtrace::Backtrace::force_capture();
            tracing::error!("{panic_info}\n{backtrace}");

            // We also need to print to stderr directly for when using `$logTrace` because
            // the message won't be sent to the client.
            // But don't use `eprintln` because `eprintln` itself may panic if the pipe is broken.
            let mut stderr = std::io::stderr().lock();
            writeln!(stderr, "{panic_info}\n{backtrace}").ok();

            try_show_message(
                "The ZubanLS server exited with a panic. Check the logs for more details."
                    .to_string(),
                MessageType::ERROR,
            )
            .ok();
            */
            todo!()
        }));

        event_loop_thread(move || {
            Self::event_loop(
                //&self.client_capabilities,
                //self.session,
            )?;
            //self.connection.close()?;
            Ok(())
        })
    }

    fn event_loop(//_client_capabilities: &ClientCapabilities,
        //mut session: Session,
    ) -> anyhow::Result<()> {
        let (connection, threads) = lsp_server::Connection::stdio();
        let mut global_state = GlobalState::new(connection.sender);
        for msg in connection.receiver.iter() {
            use lsp_types::notification::Notification;
            if matches!(
                &msg,
                lsp_server::Message::Notification(lsp_server::Notification { method, .. })
                if method == lsp_types::notification::Exit::METHOD
            ) {
                return Ok(());
            }

            match msg {
                Message::Request(r) => global_state.on_request(r),
                Message::Notification(n) => global_state.on_notification(n),
                Message::Response(r) => global_state.complete_request(r),
            }
        }

        Ok(())
    }

    /*
    fn find_best_position_encoding(client_capabilities: &ClientCapabilities) -> PositionEncoding {
        client_capabilities
            .general
            .as_ref()
            .and_then(|general_capabilities| general_capabilities.position_encodings.as_ref())
            .and_then(|encodings| {
                encodings
                    .iter()
                    .filter_map(|encoding| PositionEncoding::try_from(encoding).ok())
                    .max() // this selects the highest priority position encoding
            })
            .unwrap_or_default()
    }

    fn server_capabilities(position_encoding: PositionEncoding) -> ServerCapabilities {
        ServerCapabilities {
            position_encoding: Some(position_encoding.into()),
            diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
                identifier: Some(DIAGNOSTIC_NAME.into()),
                ..Default::default()
            })),
            text_document_sync: Some(TextDocumentSyncCapability::Options(
                TextDocumentSyncOptions {
                    open_close: Some(true),
                    change: Some(TextDocumentSyncKind::INCREMENTAL),
                    ..Default::default()
                },
            )),
            ..Default::default()
        }
    }
    */
}
pub(crate) struct NotificationDispatcher<'a> {
    pub(crate) not: Option<lsp_server::Notification>,
    pub(crate) global_state: &'a mut GlobalState,
}

pub(crate) struct GlobalState {
    sender: Sender<lsp_server::Message>,
}

impl GlobalState {
    fn new(sender: Sender<lsp_server::Message>) -> Self {
        GlobalState { sender }
    }

    /// Handles an incoming notification.
    fn on_notification(&mut self, not: lsp_server::Notification) {
        use lsp_types::notification::*;

        NotificationDispatcher {
            not: Some(not),
            global_state: self,
        }
        //.on_sync_mut::<Cancel>(GlobalState::handle_cancel)
        //.on_sync_mut::<WorkDoneProgressCancel>(GlobalState::handle_work_done_progress_cancel)
        .on_sync_mut::<DidOpenTextDocument>(GlobalState::handle_did_open_text_document)
        .on_sync_mut::<DidChangeTextDocument>(GlobalState::handle_did_change_text_document)
        .on_sync_mut::<DidCloseTextDocument>(GlobalState::handle_did_close_text_document)
        .on_sync_mut::<DidSaveTextDocument>(GlobalState::handle_did_save_text_document)
        //.on_sync_mut::<DidChangeWorkspaceFolders>(GlobalState::handle_did_change_workspace_folders)
        //.on_sync_mut::<notifs::DidChangeWatchedFiles>(GlobalState::handle_did_change_watched_files)
        .finish();
    }

    fn on_request(&mut self, req: Request) {
        todo!()
    }
    fn complete_request(&mut self, response: lsp_server::Response) {
        todo!()
    }
}

impl NotificationDispatcher<'_> {
    pub(crate) fn on_sync_mut<N>(
        &mut self,
        f: fn(&mut GlobalState, N::Params) -> anyhow::Result<()>,
    ) -> &mut Self
    where
        N: lsp_types::notification::Notification,
        N::Params: serde::de::DeserializeOwned + Send + std::fmt::Debug,
    {
        let not = match self.not.take() {
            Some(it) => it,
            None => return self,
        };

        let _guard = tracing::info_span!("notification", method = ?not.method).entered();

        let params = match not.extract::<N::Params>(N::METHOD) {
            Ok(it) => it,
            Err(ExtractError::JsonError { method, error }) => {
                panic!("Invalid request\nMethod: {method}\n error: {error}",)
            }
            Err(ExtractError::MethodMismatch(not)) => {
                self.not = Some(not);
                return self;
            }
        };

        tracing::debug!(?params);

        /*
        let _pctx = stdx::panic_context::enter(format!(
            "\nversion: {}\nnotification: {}",
            version(),
            N::METHOD
        ));
        */
        if let Err(e) = f(self.global_state, params) {
            tracing::error!(handler = %N::METHOD, error = %e, "notification handler failed");
        }
        self
    }

    pub(crate) fn finish(&mut self) {
        if let Some(not) = &self.not {
            if !not.method.starts_with("$/") {
                tracing::error!("unhandled notification: {:?}", not);
            }
        }
    }
}
