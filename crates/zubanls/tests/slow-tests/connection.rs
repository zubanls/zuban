use std::{cell::Cell, path::Path, str::FromStr, time::Duration};

use crossbeam_channel::RecvTimeoutError;
use lsp_server::Message;
use lsp_types::{notification::Notification as _, InitializeResult, Uri, WorkspaceFolder};
use serde::{de::DeserializeOwned, Serialize};

pub(crate) fn path_to_uri(path: &str) -> Uri {
    if cfg!(target_os = "windows") {
        Uri::from_str(&path.replace('\\', "/"))
    } else {
        Uri::from_str(path)
    }.unwrap()
}

pub(crate) struct Connection {
    client: lsp_server::Connection,
    server_thread: Option<std::thread::JoinHandle<()>>,
    request_id_counter: Cell<i32>,
}

impl Connection {
    pub(crate) fn new() -> Self {
        Self::new_internal(false)
    }

    pub(crate) fn with_avoids_panics_and_messages_instead() -> Self {
        Self::new_internal(true)
    }

    fn new_internal(panic_should_message_not_abort: bool) -> Self {
        logging_config::setup_logging_for_tests();
        let (connection1, connection2) = lsp_server::Connection::memory();

        let server_thread = Some(std::thread::spawn(move || {
            let cloned_sender = connection1.sender.clone();
            let typeshed_path = Some(test_utils::typeshed_path());
            if panic_should_message_not_abort {
                let maybe_paniced = std::panic::catch_unwind(|| {
                    zubanls::run_server_with_custom_connection(connection1, typeshed_path, || {
                        Ok(())
                    })
                    .expect("Should not error");
                });
                if let Err(err) = maybe_paniced {
                    // Send the panic explicitly
                    let _ = cloned_sender.send(lsp_server::Message::Notification(
                        lsp_server::Notification {
                            method: lsp_types::notification::ShowMessage::METHOD.into(),
                            params: serde_json::to_value(lsp_types::ShowMessageParams {
                                typ: lsp_types::MessageType::ERROR,
                                message: format!("ZubanLS test paniced: {err:?}"),
                            })
                            .unwrap(),
                        },
                    ));
                }
            } else {
                zubanls::run_server_with_custom_connection(connection1, typeshed_path, || Ok(()))
                    .expect("Should not error");
            }
        }));

        Self {
            client: connection2,
            server_thread,
            request_id_counter: Cell::new(0),
        }
    }

    pub(crate) fn initialized(panic_should_message_not_abort: bool, roots: &[&str]) -> Self {
        let slf = Self::new_internal(panic_should_message_not_abort);
        slf.initialize(roots);
        slf
    }

    pub(crate) fn initialize(&self, roots: &[&str]) -> InitializeResult {
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
            Err(err) => panic!("Expected a message, but got: {err:?}"),
        }
    }

    fn expect_notification(&self) -> lsp_server::Notification {
        match self.recv_timeout() {
            Ok(Message::Notification(not)) => not,
            Ok(msg) => panic!("Unexpected message, expected notification: {msg:?}"),
            Err(err) => panic!("Expected a message, but got: {err:?}"),
        }
    }

    pub(crate) fn expect_notification_message(&self) -> lsp_types::ShowMessageParams {
        let not = self.expect_notification();
        not.extract::<lsp_types::ShowMessageParams>("window/showMessage")
            .unwrap()
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
