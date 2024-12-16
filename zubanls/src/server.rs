//! Scheduling, I/O, and API endpoints.

// The new PanicInfoHook name requires MSRV >= 1.82
#[allow(deprecated)]
use std::panic::PanicInfo;

use crossbeam_channel::Sender;
use lsp_server::{Connection, ExtractError, Message, Request};
use lsp_types::{
    request::DocumentDiagnosticRequest, ClientCapabilities, Diagnostic, DiagnosticOptions,
    DiagnosticServerCapabilities, DocumentDiagnosticReport, DocumentDiagnosticReportResult,
    MessageType, ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
    TextDocumentSyncOptions, Uri,
};
use serde::{de::DeserializeOwned, Serialize};

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

pub(crate) fn event_loop() -> anyhow::Result<()> {
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
    threads.join()?;
    Ok(())
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
struct NotificationDispatcher<'a> {
    not: Option<lsp_server::Notification>,
    global_state: &'a mut GlobalState,
}

pub(crate) struct GlobalState {
    pub sender: Sender<lsp_server::Message>,
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

    fn on_request(&mut self, request: Request) {
        RequestDispatcher {
            request: Some(request),
            global_state: self,
        }
        .on_sync_mut::<DocumentDiagnosticRequest>(GlobalState::handle_document_diagnostics)
        .finish();
    }

    fn respond(&mut self, response: lsp_server::Response) {
        if let Some(err) = &response.error {
            if err.message.starts_with("server panicked") {
                //self.poke_rust_analyzer_developer(format!("{}, check the log", err.message))
            }
        }
        self.sender.send(response.into()).unwrap()
    }

    fn complete_request(&mut self, _response: lsp_server::Response) {
        todo!()
    }
}

impl NotificationDispatcher<'_> {
    fn on_sync_mut<N>(
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

    fn finish(&mut self) {
        if let Some(not) = &self.not {
            if !not.method.starts_with("$/") {
                tracing::error!("unhandled notification: {:?}", not);
            }
        }
    }
}

struct RequestDispatcher<'a> {
    request: Option<lsp_server::Request>,
    global_state: &'a mut GlobalState,
}

impl RequestDispatcher<'_> {
    fn on_sync_mut<R>(
        &mut self,
        f: fn(&mut GlobalState, R::Params) -> anyhow::Result<R::Result>,
    ) -> &mut Self
    where
        R: lsp_types::request::Request,
        R::Params: DeserializeOwned + std::panic::UnwindSafe + std::fmt::Debug,
        R::Result: Serialize,
    {
        let (req, params, _panic_context) = match self.parse::<R>() {
            Some(it) => it,
            None => return self,
        };
        let _guard =
            tracing::info_span!("request", method = ?req.method, "request_id" = ?req.id).entered();
        tracing::debug!(?params);
        let result = {
            //let _pctx = stdx::panic_context::enter(panic_context);
            f(self.global_state, params)
        };
        if let Ok(response) = result_to_response::<R>(req.id, result) {
            self.global_state.respond(response);
        }

        self
    }

    fn parse<R>(&mut self) -> Option<(lsp_server::Request, R::Params, String)>
    where
        R: lsp_types::request::Request,
        R::Params: DeserializeOwned + std::fmt::Debug,
    {
        let req = self.request.take_if(|it| it.method == R::METHOD)?;
        let res = from_json(R::METHOD, &req.params);
        match res {
            Ok(params) => {
                let panic_context = format!(
                    "\nversion: {}\nrequest: {} {params:#?}",
                    version(),
                    R::METHOD
                );
                Some((req, params, panic_context))
            }
            Err(err) => {
                let response = lsp_server::Response::new_err(
                    req.id,
                    lsp_server::ErrorCode::InvalidParams as i32,
                    err.to_string(),
                );
                self.global_state.respond(response);
                None
            }
        }
    }

    fn finish(&mut self) {
        if let Some(req) = self.request.take() {
            tracing::error!("unknown request: {:?}", req);
            let response = lsp_server::Response::new_err(
                req.id,
                lsp_server::ErrorCode::MethodNotFound as i32,
                "unknown request".to_owned(),
            );
            self.global_state.respond(response);
        }
    }
}

pub fn from_json<T: DeserializeOwned>(
    what: &'static str,
    json: &serde_json::Value,
) -> anyhow::Result<T> {
    serde_json::from_value(json.clone())
        .map_err(|e| anyhow::format_err!("Failed to deserialize {what}: {e}; {json}"))
}

struct Cancelled(); // TODO currently unused

fn result_to_response<R>(
    id: lsp_server::RequestId,
    result: anyhow::Result<R::Result>,
) -> Result<lsp_server::Response, Cancelled>
where
    R: lsp_types::request::Request,
    R::Params: DeserializeOwned,
    R::Result: Serialize,
{
    let res = match result {
        Ok(resp) => lsp_server::Response::new_ok(id, &resp),
        /*
        Err(e) => match e.downcast::<LspError>() {
            Ok(lsp_error) => lsp_server::Response::new_err(id, lsp_error.code, lsp_error.message),
            Err(e) => match e.downcast::<Cancelled>() {
                Ok(cancelled) => return Err(cancelled),
                Err(e) => lsp_server::Response::new_err(
                    id,
                    lsp_server::ErrorCode::InternalError as i32,
                    e.to_string(),
                ),
            },
        },
        */
        Err(e) => lsp_server::Response::new_err(
            id,
            lsp_server::ErrorCode::InternalError as i32,
            e.to_string(),
        ),
    };
    Ok(res)
}
