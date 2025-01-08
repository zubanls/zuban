//! Scheduling, I/O, and API endpoints.

use std::panic::PanicHookInfo;
use std::{path::PathBuf, rc::Rc};
use vfs::{LocalFS, NotifyEvent, Vfs};

use config::ProjectOptions;
use crossbeam_channel::{never, select, Sender};
use lsp_server::{Connection, ExtractError, Message, Request};
use lsp_types::Uri;
use serde::{de::DeserializeOwned, Serialize};
use zuban_python::Project;

use crate::capabilities::{server_capabilities, ClientCapabilities};

fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

pub fn run_server_with_custom_connection(
    connection: Connection,
    cleanup: impl FnOnce() -> anyhow::Result<()>,
) -> anyhow::Result<()> {
    tracing::info!("Server version {} will start", version());

    let (initialize_id, initialize_params) = match connection.initialize_start() {
        Ok(it) => it,
        Err(e) => {
            if e.channel_is_disconnected() {
                cleanup()?;
            }
            return Err(e.into());
        }
    };

    tracing::info!("InitializeParams: {}", initialize_params);
    #[expect(deprecated)]
    let lsp_types::InitializeParams {
        root_uri,
        capabilities,
        workspace_folders,
        client_info,
        ..
    } = from_json::<lsp_types::InitializeParams>("InitializeParams", &initialize_params)?;

    if let Some(client_info) = &client_info {
        tracing::info!(
            "Client '{}' {}",
            client_info.name,
            client_info.version.as_deref().unwrap_or_default()
        );
    }

    let workspace_roots = workspace_folders
        .map(|workspaces| {
            workspaces
                .into_iter()
                .map(|workspace| patch_path_prefix(&workspace.uri))
                .collect::<Vec<_>>()
        })
        .filter(|workspaces| !workspaces.is_empty());
    let workspace_roots = match workspace_roots {
        Some(r) => r,
        None => {
            let root_path = match root_uri.as_ref().map(patch_path_prefix) {
                Some(it) => it,
                None => {
                    let cwd = std::env::current_dir()?;
                    cwd.into_os_string().into_string().map_err(|e| {
                        anyhow::anyhow!("Invalid non utf-8 working directory: {e:?}")
                    })?
                }
            };
            vec![root_path.clone()]
        }
    };

    let client_capabilities = ClientCapabilities::new(capabilities);
    let server_capabilities = server_capabilities(&client_capabilities);

    let initialize_result = lsp_types::InitializeResult {
        capabilities: server_capabilities,
        server_info: Some(lsp_types::ServerInfo {
            name: String::from("zubanls"),
            version: Some(version().to_string()),
        }),
        offset_encoding: None,
    };

    let initialize_result = serde_json::to_value(initialize_result).unwrap();

    if let Err(e) = connection.initialize_finish(initialize_id, initialize_result) {
        if e.channel_is_disconnected() {
            cleanup()?;
        }
        return Err(e.into());
    }

    // If the io_threads have an error, there's usually an error on the main
    // loop too because the channels are closed. Ensure we report both errors.
    event_loop(client_capabilities, connection, workspace_roots)?;
    cleanup()?;
    tracing::info!("Server did successfully shut down");
    Ok(())
}

pub fn run_server() -> anyhow::Result<()> {
    let (connection, io_threads) = Connection::stdio();
    run_server_with_custom_connection(connection, || Ok(io_threads.join()?))
}

enum Event {
    Lsp(Message),
    Notify(NotifyEvent),
}

fn event_loop(
    capabilities: ClientCapabilities,
    connection: lsp_server::Connection,
    roots: Vec<String>,
) -> anyhow::Result<()> {
    let mut global_state = GlobalState::new(connection.sender, capabilities, roots);
    loop {
        let event = select! {
            recv(connection.receiver) -> msg => Event::Lsp(msg?),
            recv(global_state.vfs.notify_receiver().unwrap_or(&never())) -> msg =>
                Event::Notify(msg?),
        };
        match event {
            Event::Lsp(msg) => {
                use lsp_types::notification::Notification;
                match msg {
                    Message::Request(r) => global_state.on_request(r),
                    Message::Notification(n) => {
                        if n.method == lsp_types::notification::Exit::METHOD {
                            return Ok(());
                        }
                        global_state.on_notification(n)
                    }
                    Message::Response(r) => global_state.complete_request(r),
                }
            }
            Event::Notify(event) => {
                global_state.on_notify_event(event);
                // Check all events in the Notify queue
                while let Ok(next) = global_state.vfs.notify_receiver().unwrap().try_recv() {
                    global_state.on_notify_event(next);
                }
            }
        }
    }
}

/*
let client_capabilities = init_params.capabilities;
let position_encoding = Self::find_best_position_encoding(&client_capabilities);
let server_capabilities = Self::server_capabilities(position_encoding);


if let Some(trace) = init_params.trace {
    crate::trace::set_trace_value(trace);
}

...

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

*/

struct NotificationDispatcher<'a> {
    not: Option<lsp_server::Notification>,
    global_state: &'a mut GlobalState,
}

pub(crate) struct GlobalState {
    pub sender: Sender<lsp_server::Message>,
    pub roots: Vec<String>,
    pub vfs: Rc<dyn Vfs>,
    pub project: Option<Project>,
    pub shutdown_requested: bool,
}

impl GlobalState {
    fn new(
        sender: Sender<lsp_server::Message>,
        _capabilities: ClientCapabilities,
        roots: Vec<String>,
    ) -> Self {
        let vfs = LocalFS::with_watcher();
        for r in &roots {
            vfs.walk_and_watch_dirs(r);
        }
        GlobalState {
            sender,
            roots,
            project: None,
            vfs: Rc::new(vfs),
            shutdown_requested: false,
        }
    }

    pub(crate) fn project(&mut self) -> &mut Project {
        let project = &mut self.project;
        if let Some(p) = project {
            return p;
        } else {
            let first_root = self
                .roots
                .first()
                .expect("There should always be at least one root at this point");
            let mut config =
                config_searcher::find_workspace_config(first_root).unwrap_or_else(|err| {
                    use lsp_types::{
                        notification::{Notification, ShowMessage},
                        MessageType, ShowMessageParams,
                    };
                    let not = lsp_server::Notification::new(
                        ShowMessage::METHOD.to_owned(),
                        ShowMessageParams {
                            typ: MessageType::WARNING,
                            message: err.to_string(),
                        },
                    );
                    self.sender
                        .send(lsp_server::Message::Notification(not))
                        .unwrap();
                    ProjectOptions::default()
                });

            tracing::info!("Using workspace roots {:?}", &self.roots);
            // I'm not sure if this is correct. The problem is that the mypy_path currently does
            // two things:
            //
            // 1. Adds it as a workspace to be type-checked
            // 2. Adds it to the "sys path"
            //
            // It's questionable that we want those two things. And maybe there will also be a need
            // for the type checker to understand what the mypy_path originally was.
            config.settings.mypy_path = self.roots.clone();

            *project = Some(Project::without_watcher(config));
            project.as_mut().unwrap()
        }
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
        //.on_sync_mut::<DidChangeWorkspaceFolders>(GlobalState::handle_did_change_workspace_folders)
        //.on_sync_mut::<notifs::DidChangeWatchedFiles>(GlobalState::handle_did_change_watched_files)
        .finish();
    }

    fn on_request(&mut self, request: Request) {
        if self.shutdown_requested {
            self.respond(lsp_server::Response::new_err(
                request.id.clone(),
                lsp_server::ErrorCode::InvalidRequest as i32,
                "Shutdown already requested.".to_owned(),
            ));
            return;
        }

        use lsp_types::request::*;

        RequestDispatcher {
            request: Some(request),
            global_state: self,
        }
        .on_sync_mut::<DocumentDiagnosticRequest>(GlobalState::handle_document_diagnostics)
        .on_sync_mut::<Shutdown>(GlobalState::handle_shutdown)
        .finish();
    }

    fn on_notify_event(&mut self, event: NotifyEvent) {
        if let Some(project) = &mut self.project {
            match event {
                Ok(event) => {
                    tracing::debug!("Notify Event: {event:?}")
                    /*
                    if let EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_) = event.kind {
                        project.invalidate_path()
                    }
                    */
                }
                Err(err) => {
                    tracing::error!(
                        "Invalidating project, because of a notify event error: {err:?}"
                    );
                    self.project = None;
                }
            }
        }
    }

    fn respond(&mut self, response: lsp_server::Response) {
        if let Some(err) = &response.error {
            if err.message.starts_with("server panicked") {
                //self.poke_rust_analyzer_developer(format!("{}, check the log", err.message))
            }
        }
        self.sender.send(response.into()).unwrap()
    }

    fn complete_request(&mut self, response: lsp_server::Response) {
        tracing::error!("unhandled request: {:?}", response);
    }

    pub(crate) fn uri_to_path<'uri>(&self, uri: &'uri lsp_types::Uri) -> &'uri str {
        uri.path().as_str()
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
        Err(e) => match e.downcast::<LspError>() {
            Ok(lsp_error) => lsp_server::Response::new_err(id, lsp_error.code, lsp_error.message),
            Err(e) => match e.downcast::<u8/*TODO Cancelled*/>() {
                Ok(_cancelled) => todo!(), // return Err(cancelled),
                Err(e) => lsp_server::Response::new_err(
                    id,
                    lsp_server::ErrorCode::InternalError as i32,
                    e.to_string(),
                ),
            },
        },
    };
    Ok(res)
}

#[derive(Debug)]
pub(crate) struct LspError {
    pub(crate) code: i32,
    pub(crate) message: String,
}

impl std::fmt::Display for LspError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Language Server request failed with {}. ({})",
            self.code, self.message
        )
    }
}

impl std::error::Error for LspError {}

fn patch_path_prefix(path: &Uri) -> String {
    let path = path.as_str();
    use std::path::{Component, Prefix};
    if cfg!(windows) {
        // VSCode might report paths with the file drive in lowercase, but this can mess
        // with env vars set by tools and build scripts executed by r-a such that it invalidates
        // cargo's compilations unnecessarily. https://github.com/rust-lang/rust-analyzer/issues/14683
        // So we just uppercase the drive letter here unconditionally.
        // (doing it conditionally is a pain because std::path::Prefix always reports uppercase letters on windows)
        let buf = PathBuf::from(path);
        let mut comps = buf.components();
        match comps.next() {
            Some(Component::Prefix(prefix)) => {
                let prefix = match prefix.kind() {
                    Prefix::Disk(d) => {
                        format!("{}:", d.to_ascii_uppercase() as char)
                    }
                    Prefix::VerbatimDisk(d) => {
                        format!(r"\\?\{}:", d.to_ascii_uppercase() as char)
                    }
                    _ => return path.to_string(),
                };
                let mut path = PathBuf::new();
                path.push(prefix);
                path.extend(comps);
                // The path before was utf-8, so we can unwrap.
                path.into_os_string().into_string().unwrap()
            }
            _ => path.to_string(),
        }
    } else {
        path.to_string()
    }
}

#[test]
#[cfg(windows)]
fn patch_path_prefix_works() {
    assert_eq!(
        patch_path_prefix(r"c:\foo\bar".into()),
        PathBuf::from(r"C:\foo\bar")
    );
    assert_eq!(
        patch_path_prefix(r"\\?\c:\foo\bar".into()),
        PathBuf::from(r"\\?\C:\foo\bar")
    );
}
