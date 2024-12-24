use std::{cell::Cell, str::FromStr, time::Duration};

use crossbeam_channel::RecvTimeoutError;
use lsp_server::Message;
use lsp_types::{InitializeResult, Uri};
use serde::{de::DeserializeOwned, Serialize};

pub(crate) struct Connection {
    client: lsp_server::Connection,
    server_thread: Option<std::thread::JoinHandle<()>>,
    request_id_counter: Cell<i32>,
}

impl Connection {
    pub(crate) fn new() -> Self {
        logging_config::setup_logging_for_tests();
        let (connection1, connection2) = lsp_server::Connection::memory();

        let server_thread = Some(std::thread::spawn(move || {
            zubanls::run_server_with_custom_connection(connection1, || Ok(()))
                .expect("Should not error");
        }));

        Self {
            client: connection2,
            server_thread,
            request_id_counter: Cell::new(0),
        }
    }

    pub(crate) fn initialized() -> Self {
        let slf = Self::new();
        slf.initialize();
        slf
    }

    pub(crate) fn initialize(&self) -> InitializeResult {
        #[expect(deprecated)]
        let initialize_params = lsp_types::InitializeParams {
            root_uri: Some(Uri::from_str("file:///foo/bar").unwrap()),
            capabilities: lsp_types::ClientCapabilities {
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
                ..Default::default()
            },
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

    pub(crate) fn request<R>(&self, params: R::Params) -> R::Result
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
        R::Result: DeserializeOwned,
    {
        let response = self.request_with_response::<R>(params);
        if let Some(error) = response.error {
            panic!("Unexpected error: {error:?}")
        }
        let value = response.result.expect("Expected result");
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

    fn send(&self, message: impl Into<Message>) {
        self.client
            .sender
            .send(message.into())
            .expect("Expected to be able to send a message");
    }

    fn expect_response(&self) -> lsp_server::Response {
        match self.recv_timeout() {
            Ok(Message::Response(response)) => response,
            Ok(msg) => panic!("Unexpected message, expected response: {msg:?}"),
            Err(err) => panic!("Expected a message, but got: {err:?}"),
        }
    }

    fn recv_timeout(&self) -> Result<Message, RecvTimeoutError> {
        let timeout = Duration::from_secs(5);
        self.client.receiver.recv_timeout(timeout)
    }

    pub(crate) fn shutdown_and_exit(&self) {
        self.request::<lsp_types::request::Shutdown>(());
        self.notify::<lsp_types::notification::Exit>(());
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
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
