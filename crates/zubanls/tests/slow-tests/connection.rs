use std::{cell::Cell, path::Path, str::FromStr, time::Duration};

use crossbeam_channel::RecvTimeoutError;
use lsp_server::Message;
use lsp_types::{
    DiagnosticClientCapabilities, DocumentSymbolClientCapabilities, InitializeResult,
    ServerCapabilities, TextDocumentClientCapabilities, Uri, WorkspaceFolder,
};
use serde::{Serialize, de::DeserializeOwned};
use serde_json::Value;

pub(crate) fn path_to_uri(path: &str) -> Uri {
    assert!(!path.starts_with("file:"));
    // URI's are always absolute within LSP
    let path = format!("file://{path}");
    let uri = if cfg!(target_os = "windows") {
        Uri::from_str(&path.replace('\\', "/"))
    } else {
        Uri::from_str(&path)
    }
    .unwrap();
    assert!(!uri.is_relative());
    uri
}

pub(crate) struct Connection {
    client: lsp_server::Connection,
    server_thread: Option<std::thread::JoinHandle<()>>,
    request_id_counter: Cell<i32>,
    pub server_capabilities: Option<ServerCapabilities>,
}

impl Connection {
    pub(crate) fn new() -> Self {
        logging_config::setup_logging_for_tests();
        let (connection1, connection2) = lsp_server::Connection::memory();

        let server_thread = Some(std::thread::spawn(move || {
            let typeshed_path = Some(test_utils::typeshed_path());
            zubanls::run_server_with_custom_connection(connection1, typeshed_path, || Ok(()))
                .expect("Should not error");
        }));

        Self {
            client: connection2,
            server_thread,
            request_id_counter: Cell::new(0),
            server_capabilities: None,
        }
    }

    pub(crate) fn initialized(
        roots: &[&str],
        position_encodings: Option<Vec<lsp_types::PositionEncodingKind>>,
        pull_diagnostics: bool,
    ) -> Self {
        let mut slf = Self::new();
        let response = slf.initialize(roots, position_encodings, pull_diagnostics);
        slf.server_capabilities = Some(response.capabilities);
        slf
    }

    pub(crate) fn initialize(
        &self,
        roots: &[&str],
        position_encodings: Option<Vec<lsp_types::PositionEncodingKind>>,
        pull_diagnostics: bool,
    ) -> InitializeResult {
        let capabilities = lsp_types::ClientCapabilities {
            workspace: Some(lsp_types::WorkspaceClientCapabilities {
                did_change_watched_files: Some(
                    lsp_types::DidChangeWatchedFilesClientCapabilities {
                        dynamic_registration: Some(true),
                        relative_pattern_support: None,
                    },
                ),
                workspace_edit: Some(lsp_types::WorkspaceEditClientCapabilities {
                    resource_operations: Some(vec![
                        lsp_types::ResourceOperationKind::Create,
                        lsp_types::ResourceOperationKind::Delete,
                        lsp_types::ResourceOperationKind::Rename,
                    ]),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            general: Some(lsp_types::GeneralClientCapabilities {
                position_encodings,
                ..Default::default()
            }),
            text_document: Some(TextDocumentClientCapabilities {
                diagnostic: pull_diagnostics.then(DiagnosticClientCapabilities::default),
                document_symbol: Some(DocumentSymbolClientCapabilities {
                    hierarchical_document_symbol_support: Some(true),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        };
        let initialize_params = lsp_types::InitializeParams {
            workspace_folders: Some(
                roots
                    .iter()
                    .map(|root| WorkspaceFolder {
                        uri: path_to_uri(root),
                        name: Path::new(root)
                            .file_name()
                            .unwrap()
                            .to_str()
                            .unwrap()
                            .to_owned(),
                    })
                    .collect(),
            ),
            capabilities,
            ..Default::default()
        };
        let response = self.request::<lsp_types::request::Initialize>(initialize_params);
        self.notify::<lsp_types::notification::Initialized>(lsp_types::InitializedParams {});
        response
    }

    pub(crate) fn request_with_response<R>(&self, params: R::Params) -> lsp_server::Response
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
    {
        let id = self.request_id_counter.get();
        self.request_id_counter.set(id.wrapping_add(1));

        let r = lsp_server::Request::new(id.into(), R::METHOD.to_string(), params);
        self.send(r);

        self.expect_response()
    }

    pub(crate) fn request_with_expected_error<R>(
        &self,
        params: R::Params,
    ) -> lsp_server::ResponseError
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
    {
        let response = self.request_with_response::<R>(params);
        if let Some(result) = response.result {
            panic!("Unexpected result: {result:?}")
        }
        response.error.expect("Expected error")
    }

    pub fn request_with_expected_response<R>(&self, params: R::Params) -> Value
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
    {
        let response = self.request_with_response::<R>(params);
        if let Some(error) = response.error {
            panic!("Unexpected error: {error:?}")
        }
        response.result.expect("Expected result")
    }

    pub(crate) fn request<R>(&self, params: R::Params) -> R::Result
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
        R::Result: DeserializeOwned,
    {
        let value = self.request_with_expected_response::<R>(params);
        serde_json::from_value(value.clone())
            .unwrap_or_else(|e| panic!("Failed to deserialize {}: {e}; {value}", R::METHOD))
    }

    pub(crate) fn notify<R>(&self, params: R::Params)
    where
        R: lsp_types::notification::Notification,
        R::Params: Serialize,
    {
        self.send(lsp_server::Notification::new(R::METHOD.to_string(), params));
    }

    pub(crate) fn send(&self, message: impl Into<Message>) {
        self.client
            .sender
            .send(message.into())
            .expect("Expected to be able to send a message");
    }

    fn expect_response(&self) -> lsp_server::Response {
        match self.recv_timeout() {
            Ok(Message::Response(response)) => response,
            Ok(msg) => panic!("Unexpected message, expected response: {msg:?}"),
            Err(err) => {
                tracing::error!("Why no response");
                panic!("Expected a message, but got: {err:?}")
            }
        }
    }

    pub fn expect_notification<N: lsp_types::notification::Notification>(&self) -> N::Params {
        match self.recv_timeout() {
            Ok(Message::Notification(not)) => not
                .extract::<N::Params>(N::METHOD)
                .unwrap_or_else(|err| panic!("Wanted {}, got {err:?}", N::METHOD)),
            Ok(msg) => panic!("Unexpected message, expected notification: {msg:?}"),
            Err(err) => {
                tracing::error!("Why no notification, expected {}", N::METHOD);
                panic!("Expected the notification {}, but got: {err:?}", N::METHOD)
            }
        }
    }

    pub(crate) fn expect_notification_message(&self) -> lsp_types::ShowMessageParams {
        self.expect_notification::<lsp_types::notification::ShowMessage>()
    }

    fn recv_timeout(&self) -> Result<Message, RecvTimeoutError> {
        let timeout = Duration::from_secs(5);
        self.client.receiver.recv_timeout(timeout)
    }

    pub(crate) fn shutdown_and_exit(&self) {
        tracing::info!("Initiate shutdown sequence");
        self.request::<lsp_types::request::Shutdown>(());
        self.notify::<lsp_types::notification::Exit>(());
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        if let Ok(msg) = self.client.receiver.try_recv() {
            panic!("Wanted to drop the connection, but the message {msg:?} appeared");
        }
        assert!(self.client.receiver.is_empty());
        if let Some(server_thread) = self.server_thread.take() {
            let mut counter = 0;
            const MAX_MS: usize = 5000;
            while !server_thread.is_finished() && counter < MAX_MS {
                std::thread::sleep(Duration::from_millis(1));
                counter += 1;
            }
            if counter >= MAX_MS {
                panic!("A thread was not joined properly");
            }
            server_thread
                .join()
                .expect("The thread was not properly finished");
        }
        assert!(self.client.sender.is_empty());
    }
}
