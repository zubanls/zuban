//! Scheduling, I/O, and API endpoints.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::atomic::AtomicI64;
use std::sync::{Arc, RwLock};

use anyhow::bail;
use config::ProjectOptions;
use crossbeam_channel::{Receiver, Sender, never, select};
use fluent_uri::Scheme;
use lsp_server::{Connection, ExtractError, Message, Request};
use lsp_types::Uri;
use lsp_types::notification::Notification as _;
use notify::EventKind;
use serde::{Serialize, de::DeserializeOwned};
use vfs::{LocalFS, NormalizedPath, NotifyEvent, PathWithScheme, VfsHandler as _};
use zuban_python::{Mode, PanicRecovery, Project};

use crate::capabilities::{ClientCapabilities, server_capabilities};
use crate::notebooks::Notebooks;
use crate::notification_handlers::TestPanic;
use crate::panic_hooks;

// Since we currently don't do garbage collection, we simply delete the project and reindex,
// because it's not that expensive after a specific amount of diagnostics.
const REINDEX_AFTER_N_DIAGNOSTICS: usize = 1000;

pub static GLOBAL_NOTIFY_EVENT_COUNTER: AtomicI64 = AtomicI64::new(0);

fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

pub fn run_server_with_custom_connection(
    connection: Connection,
    typeshed_path: Option<Arc<NormalizedPath>>,
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

    let workspace_roots = if let Some(workspaces) = workspace_folders {
        Some(
            workspaces
                .into_iter()
                .map(|workspace| patch_path_prefix(&workspace.uri))
                .collect::<anyhow::Result<Rc<[String]>>>()?,
        )
    } else {
        None
    };
    let workspace_roots = match workspace_roots.filter(|workspaces| !workspaces.is_empty()) {
        Some(r) => r,
        None => {
            let root_path = match root_uri.as_ref().map(patch_path_prefix) {
                Some(it) => it?,
                None => {
                    let cwd = std::env::current_dir()?;
                    cwd.into_os_string().into_string().map_err(|e| {
                        anyhow::anyhow!("Invalid non utf-8 working directory: {e:?}")
                    })?
                }
            };
            Rc::new([root_path.clone()])
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

    thread_local! {
        static LOCAL_SENDER: RefCell<Option<Sender<Message>>> = const { RefCell::new(None) };
    }

    // We need to use a thread local for the sender, because the hook is global and can therefore
    // be used to send something to the wrong thread.
    LOCAL_SENDER.with(|s| {
        *s.borrow_mut() = Some(connection.sender.clone());
    });

    // On panic, notify the client.
    let _hook = panic_hooks::enter(Box::new(move |panic_info| {
        use std::io::Write;

        let backtrace = std::backtrace::Backtrace::force_capture();

        // Currently std::panic::get_backtrace_style is unstable:
        // https://github.com/rust-lang/rust/issues/93346
        let use_backtrace = match std::env::var_os("RUST_BACKTRACE") {
            Some(x) if &x == "0" => false,
            None => false,
            _ => true,
        };

        // We also generally want to print to stderr when a panic happens.
        // But don't use `eprintln` because `eprintln` itself may panic if the pipe is broken.
        let mut stderr = std::io::stderr().lock();
        if use_backtrace {
            writeln!(stderr, "Panic hook: {panic_info}\n{backtrace}").ok();
        } else {
            writeln!(stderr, "Panic hook: {panic_info} ").ok();
        }

        // It's not guaranteed that we can notify the client, but we try to.
        if let Err(err) = LOCAL_SENDER.with_borrow(|sender| {
            sender
                .as_ref()
                .unwrap()
                .send(lsp_server::Message::Notification(
                    lsp_server::Notification {
                        method: lsp_types::notification::ShowMessage::METHOD.into(),
                        params: serde_json::to_value(lsp_types::ShowMessageParams {
                            typ: lsp_types::MessageType::ERROR,
                            message: format!(
                                "Zuban paniced, please open an issue on GitHub with the details:\n\
                                Version:{}\n\
                                {panic_info}\n\n\
                                {backtrace}",
                                env!("CARGO_PKG_VERSION")
                            ),
                        })
                        .unwrap(),
                    },
                ))
        }) {
            tracing::warn!("Wanted to send panic information to the client, but got {err}");
        }
        tracing::error!("Panic hook: {panic_info}\n{backtrace}");
    }));

    let mut global_state = GlobalState::new(
        &connection.sender,
        client_capabilities,
        workspace_roots.clone(),
        typeshed_path,
    );
    global_state.event_loop(&connection.receiver)?;
    tracing::info!("Server loop ended");
    cleanup()?;
    tracing::info!("Server did successfully shut down");
    Ok(())
}

pub fn run_server() -> anyhow::Result<()> {
    // TODO reenable this in the alpha in some form
    //licensing::verify_license_in_config_dir()?;

    let (connection, _io_threads) = Connection::stdio();
    run_server_with_custom_connection(connection, None, || {
        // This used to be a join, but that seems to never join in VSCode, no idea why.
        //Ok(io_threads.join()?)
        Ok(())
    })
}

struct NotificationDispatcher<'a, 'sender> {
    not: Option<lsp_server::Notification>,
    global_state: &'a mut GlobalState<'sender>,
}

pub(crate) struct GlobalState<'sender> {
    paths_that_invalidate_whole_project: HashSet<PathBuf>,
    sender: &'sender Sender<lsp_server::Message>,
    roots: Rc<[String]>,
    typeshed_path: Option<Arc<NormalizedPath>>,
    pub client_capabilities: ClientCapabilities,
    project: Option<Project>,
    panic_recovery: Option<PanicRecovery>,
    pub sent_diagnostic_count: usize,
    changed_in_memory_files: Arc<RwLock<Vec<PathWithScheme>>>,
    pub notebooks: Notebooks,
    pub shutdown_requested: bool,
}

impl<'sender> GlobalState<'sender> {
    fn new(
        sender: &'sender Sender<lsp_server::Message>,
        client_capabilities: ClientCapabilities,
        roots: Rc<[String]>,
        typeshed_path: Option<Arc<NormalizedPath>>,
    ) -> Self {
        GlobalState {
            paths_that_invalidate_whole_project: Default::default(),
            sender,
            roots,
            typeshed_path,
            client_capabilities,
            project: None,
            panic_recovery: None,
            changed_in_memory_files: Default::default(),
            notebooks: Default::default(),
            sent_diagnostic_count: 0,
            shutdown_requested: false,
        }
    }

    fn event_loop(&mut self, receiver: &Receiver<Message>) -> anyhow::Result<()> {
        loop {
            // Make sure the project is basically loaded
            self.project();

            select! {
                recv(receiver) -> msg => {
                    if self.on_lsp_message_and_return_on_shutdown(msg?) {
                        return Ok(());
                    }
                },
                recv(self.notify_receiver().unwrap_or(&never())) -> msg =>
                    self.on_notify_events(msg?)
            }
            // See comment on REINDEX_AFTER_N_DIAGNOSTICS
            if self.sent_diagnostic_count > REINDEX_AFTER_N_DIAGNOSTICS {
                self.sent_diagnostic_count = 0;
                tracing::info!("Reindex for performance reasons");
                self.recover_from_panic();
            }

            self.publish_diagnostics_if_necessary();
        }
    }

    fn notify_receiver(&self) -> Option<&Receiver<NotifyEvent>> {
        self.project.as_ref()?.vfs_handler().notify_receiver()
    }

    pub(crate) fn project(&mut self) -> &mut Project {
        let project = &mut self.project;
        if let Some(p) = project {
            p
        } else {
            let new_changed_files = self.changed_in_memory_files.clone();
            let should_push = self.client_capabilities.should_push_diagnostics();
            let vfs_handler = LocalFS::with_watcher(move |path| {
                if should_push {
                    let mut changed_files = new_changed_files.as_ref().write().unwrap();
                    // This is currently a not a set, because the order matters
                    if !changed_files.contains(&path) {
                        changed_files.push(path)
                    }
                }
            });
            let first_root = self
                .roots
                .first()
                .expect("There should always be at least one root at this point");
            let first_root = vfs_handler.unchecked_abs_path(first_root);
            let mut config = config::find_workspace_config(&vfs_handler, &first_root, |path| {
                // Watch the file itself to make sure that we can invalidate when it changes.
                let path = Path::new(&**path);
                vfs_handler.watch(path);
                // Since these are config files there should always be a parent
                let parent_dir = path.parent().unwrap();
                // This function is executed even when a file is not found. Therefore we watch the
                // directory as well, if the file suddenly gets inserted.
                // Don't delete this line of code, it might not be necessary in most cases, because
                // the base directory is typically already watched, but I'm not sure this will
                // always be the case.
                match std::fs::canonicalize(parent_dir) {
                    Ok(parent_dir) => {
                        vfs_handler.watch(&parent_dir);
                        let path = parent_dir.join(path.file_name().expect(
                            "config files where hand generated and should therefore always exist",
                        ));
                        vfs_handler.watch(&path);
                        self.paths_that_invalidate_whole_project.insert(path);
                    }
                    Err(err) => tracing::info!(
                        "Canonicalizing of path that invalidates the whole project failed: {err}"
                    ),
                }
            })
            .unwrap_or_else(|err| {
                use lsp_types::{
                    MessageType, ShowMessageParams,
                    notification::{Notification, ShowMessage},
                };
                tracing::warn!("Error while loading config: {}", err.to_string());
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
            config.settings.mypy_path.extend(
                self.roots.iter().map(|p| {
                    vfs_handler.unchecked_normalized_path(vfs_handler.unchecked_abs_path(p))
                }),
            );
            if self.typeshed_path.is_some() {
                config.settings.typeshed_path = self.typeshed_path.clone();
            }
            config
                .settings
                .try_to_apply_environment_variables(&vfs_handler, &first_root, |n| {
                    std::env::var(n)
                });

            let vfs = Box::new(vfs_handler);
            *project = Some(if let Some(recovery) = self.panic_recovery.take() {
                Project::from_recovery(vfs, config, recovery)
            } else {
                Project::new(vfs, config, Mode::LanguageServer)
            });
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
        .on_sync_mut::<DidOpenNotebookDocument>(GlobalState::handle_did_open_notebook)
        .on_sync_mut::<DidChangeNotebookDocument>(GlobalState::handle_did_change_notebook)
        .on_sync_mut::<DidCloseNotebookDocument>(GlobalState::handle_did_close_notebook)
        //.on_sync_mut::<DidChangeWorkspaceFolders>(GlobalState::handle_did_change_workspace_folders)
        //.on_sync_mut::<notifs::DidChangeWatchedFiles>(GlobalState::handle_did_change_watched_files)
        .on_sync_mut::<TestPanic>(GlobalState::test_panic)
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
        .on_sync_mut::<Completion>(GlobalState::handle_completion)
        .on_sync_mut::<ResolveCompletionItem>(GlobalState::resolve_completion_item)
        .on_sync_mut::<SignatureHelpRequest>(GlobalState::handle_signature_help)
        .on_sync_mut::<HoverRequest>(GlobalState::handle_hover)
        .on_sync_mut::<GotoDeclaration>(GlobalState::handle_goto_declaration)
        .on_sync_mut::<GotoDefinition>(GlobalState::handle_goto_definition)
        .on_sync_mut::<GotoTypeDefinition>(GlobalState::handle_goto_type_definition)
        .on_sync_mut::<GotoImplementation>(GlobalState::handle_goto_implementation)
        .on_sync_mut::<References>(GlobalState::handle_references)
        .on_sync_mut::<DocumentHighlightRequest>(GlobalState::handle_document_highlight)
        .on_sync_mut::<CodeActionRequest>(GlobalState::code_actions)
        .on_sync_mut::<PrepareRenameRequest>(GlobalState::prepare_rename)
        .on_sync_mut::<Rename>(GlobalState::rename)
        .on_sync_mut::<DocumentSymbolRequest>(GlobalState::document_symbols)
        .on_sync_mut::<WorkspaceSymbolRequest>(GlobalState::workspace_symbols)
        .on_sync_mut::<SemanticTokensFullRequest>(GlobalState::semantic_tokens)
        .on_sync_mut::<SemanticTokensRangeRequest>(GlobalState::semantic_tokens_with_range)
        .on_sync_mut::<FoldingRangeRequest>(GlobalState::folding_ranges)
        .on_sync_mut::<SelectionRangeRequest>(GlobalState::selection_ranges)
        .on_sync_mut::<Shutdown>(GlobalState::handle_shutdown)
        .finish();
    }

    fn on_lsp_message_and_return_on_shutdown(&mut self, msg: Message) -> bool {
        // It is a bit questionable that we use AssertUnwindSafe here. But the data is mostly in
        // self.project and will be cleaned up if it panics.
        tracing::trace!("New LSP message: {msg:?}");
        let mut was_message = None;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            use lsp_types::notification::Notification;
            match msg {
                Message::Request(r) => {
                    was_message = Some(r.id.clone());
                    self.on_request(r)
                }
                Message::Notification(n) => {
                    if n.method == lsp_types::notification::Exit::METHOD {
                        return true;
                    }
                    self.on_notification(n)
                }
                Message::Response(r) => self.complete_request(r),
            }
            false
        }));
        result.unwrap_or_else(|_| {
            // The error was reported
            tracing::warn!("Start panic recovery");
            if let Some(request_id) = was_message {
                self.respond(lsp_server::Response::new_err(
                    request_id,
                    lsp_server::ErrorCode::InternalError as i32,
                    format!(
                        "Server paniced, will now restart (version {})",
                        env!("CARGO_PKG_VERSION")
                    ),
                ));
            }
            self.recover_from_panic();
            tracing::info!("Recovered from panic");
            false
        })
    }

    fn recover_from_panic(&mut self) {
        self.changed_in_memory_files
            .as_ref()
            .write()
            .unwrap()
            .clear();
        if let Some(project) = self.project.take() {
            self.panic_recovery = Some(project.into_panic_recovery());
        }
    }

    fn on_notify_events(&mut self, event: NotifyEvent) {
        self.on_notify_event(event);
        // Check all events in the Notify queue
        while let Some(next) = self.notify_receiver().and_then(|n| {
            if cfg!(target_os = "windows") {
                // On Windows some events simply cause multiple events (e.g. rename), but also writes
                // to files may be a Create + Modify, so we simply wait. This is useful for tests, but
                // might also be useful in other cases, so we don't have to compute states in between
                // changes.
                n.recv_timeout(std::time::Duration::from_millis(3)).ok()
            } else {
                n.try_recv().ok()
            }
        }) {
            self.on_notify_event(next);
        }
    }

    fn on_notify_event(&mut self, event: NotifyEvent) {
        if let Some(project) = &mut self.project {
            match event {
                Ok(event) => {
                    match event.kind {
                        EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_) => {
                            // This is simply for tests
                            GLOBAL_NOTIFY_EVENT_COUNTER
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);

                            tracing::info!("Notify Event: {event:?}");
                            for path in event.paths.into_iter() {
                                if self.paths_that_invalidate_whole_project.contains(&path) {
                                    // Since invalidating the whole project is as bad as a panic we
                                    // just use that mechanism to recover from such a worst case
                                    // change. This might be something like changing the used
                                    // python version.

                                    // TODO this ignores a few events in the vec that might
                                    // invalidate additional files that get caught in the panic
                                    // recovery and reused. Currently this is not handled
                                    // correctly. If the VFS rechecks files, then it could be fine,
                                    // BUT we should document that here.
                                    tracing::info!(
                                        "Reindex because a file was changed that invalidates the whole project: {path:?}"
                                    );
                                    self.recover_from_panic();
                                    return;
                                }
                                if let Some(p) = path.to_str() {
                                    debug_assert!(path.is_absolute());
                                    let s = if cfg!(target_os = "windows")
                                        && p.starts_with(r#"\\?\"#)
                                    {
                                        &p[4..]
                                    } else {
                                        p
                                    };
                                    let p = project.vfs_handler().unchecked_abs_path(s);
                                    project.invalidate_path(&p)
                                }
                            }
                        }
                        EventKind::Access(_) => (), // Ignore access, they are probably never relevant
                        _ => tracing::debug!("Ignored Notify Event: {event:?}"),
                    }
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
        if let Some(err) = &response.error
            && err.message.starts_with("server panicked")
        {
            //self.poke_rust_analyzer_developer(format!("{}, check the log", err.message))
        }
        self.sender.send(response.into()).unwrap()
    }

    fn complete_request(&mut self, response: lsp_server::Response) {
        tracing::error!("unhandled request: {:?}", response);
    }

    fn publish_diagnostics_if_necessary(&mut self) {
        let encoding = self.client_capabilities.negotiated_encoding();
        let files = std::mem::take(&mut *self.changed_in_memory_files.as_ref().write().unwrap());
        if !files.is_empty() {
            tracing::info!(
                "Needs to publish diagnostics for {} files start at #{}",
                files.len(),
                self.sent_diagnostic_count
            );
            for path in files {
                self.sent_diagnostic_count += 1;
                let project = self.project();
                let Some(document) = project.document(&path) else {
                    tracing::info!(
                        "Wanted to publish diagnostics for {}, but it does not exist anymore",
                        path.as_uri()
                    );
                    continue;
                };
                let diagnostics = Self::diagnostics_for_file(document, encoding);
                tracing::info!(
                    "Publish diagnostics for {}, (#{} overall)",
                    path.as_uri(),
                    self.sent_diagnostic_count,
                );
                tracing::trace!(
                    "Diagnostics [{}]",
                    diagnostics
                        .iter()
                        .map(|d| {
                            format!(
                                "{}:{}-{}:{}: {}",
                                d.range.start.line,
                                d.range.start.character,
                                d.range.end.line,
                                d.range.end.character,
                                d.message,
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                let not = lsp_server::Notification::new(
                    <lsp_types::notification::PublishDiagnostics
                        as lsp_types::notification::Notification>::METHOD.to_owned(),
                    lsp_types::PublishDiagnosticsParams {
                        uri: Uri::from_str(&path.as_uri()).unwrap(),
                        diagnostics,
                        version: None,
                    }
                );
                _ = self.sender.send(not.into());
            }
        }
    }

    pub(crate) fn uri_to_path(
        project: &Project,
        uri: &lsp_types::Uri,
    ) -> anyhow::Result<PathWithScheme> {
        let (scheme, path) = unpack_uri(uri)?;
        let handler = project.vfs_handler();
        let path = handler.unchecked_abs_path_from_uri(Arc::from(path));
        Ok(if scheme.eq_lowercase("file") {
            let path = handler.normalize_rc_path(path);
            PathWithScheme::with_file_scheme(path)
        } else {
            let path = handler.unchecked_normalized_path(path);
            PathWithScheme::new(Arc::new(scheme.to_lowercase().into_boxed_str()), path)
        })
    }
}

impl<'sender> NotificationDispatcher<'_, 'sender> {
    fn on_sync_mut<N>(
        &mut self,
        f: fn(&mut GlobalState<'sender>, N::Params) -> anyhow::Result<()>,
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

        if tracing::event_enabled!(tracing::Level::DEBUG) {
            if lsp_types::notification::DidOpenTextDocument::METHOD == N::METHOD
                || lsp_types::notification::DidChangeTextDocument::METHOD == N::METHOD
            {
                // Avoid debug information in these specific cases, because we don't want to dump
                // the whole source code as debug information
                tracing::debug!(r#"notification{{method="{}"}}"#, N::METHOD);
            } else {
                tracing::debug!(?params);
            }
        }

        if let Err(e) = f(self.global_state, params) {
            tracing::error!(handler = %N::METHOD, error = %e, "notification handler failed");
        }
        self
    }

    fn finish(&mut self) {
        if let Some(not) = &self.not
            && !not.method.starts_with("$/")
        {
            tracing::error!("unhandled notification: {:?}", not);
        }
    }
}

struct RequestDispatcher<'a, 'sender> {
    request: Option<lsp_server::Request>,
    global_state: &'a mut GlobalState<'sender>,
}

impl<'sender> RequestDispatcher<'_, 'sender> {
    fn on_sync_mut<R>(
        &mut self,
        f: fn(&mut GlobalState<'sender>, R::Params) -> anyhow::Result<R::Result>,
    ) -> &mut Self
    where
        R: lsp_types::request::Request,
        R::Params: DeserializeOwned + std::panic::UnwindSafe + std::fmt::Debug,
        R::Result: Serialize,
    {
        let (req, params) = match self.parse::<R>() {
            Some(it) => it,
            None => return self,
        };
        let _guard =
            tracing::info_span!("request", method = ?req.method, "request_id" = ?req.id).entered();
        tracing::debug!(?params);
        let result = f(self.global_state, params);
        if let Ok(response) = result_to_response::<R>(req.id, result) {
            self.global_state.respond(response);
        }

        self
    }

    fn parse<R>(&mut self) -> Option<(lsp_server::Request, R::Params)>
    where
        R: lsp_types::request::Request,
        R::Params: DeserializeOwned + std::fmt::Debug,
    {
        let req = self.request.take_if(|it| it.method == R::METHOD)?;
        let res = from_json(R::METHOD, &req.params);
        match res {
            Ok(params) => Some((req, params)),
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

fn patch_path_prefix(path: &Uri) -> anyhow::Result<String> {
    let (_, path) = unpack_uri(path)?;
    use std::path::{Component, Prefix};
    if cfg!(windows) {
        // This might not be relevant for Zuban, it's from rust-analyzer, but we keep this code, it
        // seems reasonable.
        //
        // VSCode might report paths with the file drive in lowercase, but this can mess
        // with env vars set by tools and build scripts executed by r-a such that it invalidates
        // cargo's compilations unnecessarily. https://github.com/rust-lang/rust-analyzer/issues/14683
        // So we just uppercase the drive letter here unconditionally.
        // (doing it conditionally is a pain because std::path::Prefix always reports uppercase letters on windows)
        let buf = PathBuf::from(path.as_ref());
        let mut comps = buf.components();
        Ok(match comps.next() {
            Some(Component::Prefix(prefix)) => {
                let prefix = match prefix.kind() {
                    Prefix::Disk(d) => {
                        format!("{}:", d.to_ascii_uppercase() as char)
                    }
                    Prefix::VerbatimDisk(d) => {
                        format!(r"\\?\{}:", d.to_ascii_uppercase() as char)
                    }
                    _ => return Ok(path.to_string()),
                };
                let mut path = PathBuf::new();
                path.push(prefix);
                path.extend(comps);
                // The path before was utf-8, so we can unwrap.
                path.into_os_string().into_string().unwrap()
            }
            _ => path.to_string(),
        })
    } else {
        Ok(path.to_string())
    }
}

fn unpack_uri(uri: &lsp_types::Uri) -> anyhow::Result<(&Scheme, Cow<'_, str>)> {
    let Some(scheme) = uri.scheme() else {
        bail!("No scheme found in uri {}", uri.as_str())
    };

    let scheme_end = uri.scheme_end.expect("The scheme above is Some()");
    let mut p = if let Some(auth) = &uri.auth {
        uri.as_str().get(auth.start.get().get() as usize..).unwrap()
    } else {
        // + 1 for the colon in file:/
        uri.as_str().get(scheme_end.get() as usize + 1..).unwrap()
    };
    if cfg!(windows)
        && let Some(new_p) = p.strip_prefix('/')
    {
        p = new_p;
    }

    let decoded = urlencoding::decode(p)?;
    Ok((scheme, decoded))
}

#[test]
#[cfg(windows)]
fn patch_path_prefix_works() {
    use std::str::FromStr as _;
    assert_eq!(
        patch_path_prefix(&Uri::from_str(r"file:///c:/foo/bar").unwrap()).unwrap(),
        r"C:\foo\bar",
    );
    // This doesn't seem to be possible with URIs and we therefore ignore it for now.
    /*
    assert_eq!(
        &patch_path_prefix(&Uri::from_str(r"\\?\c:/foo/bar").unwrap()),
        r"\\?\C:\foo\bar",
    );
    */
}
