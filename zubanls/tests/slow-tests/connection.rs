use std::time::Duration;

use crossbeam_channel::RecvTimeoutError;
use lsp_server::Message;
use serde::{de::DeserializeOwned, Serialize};

pub(crate) struct Connection {
    client: lsp_server::Connection,
    server_thread: Option<std::thread::JoinHandle<()>>,
    request_id_counter: i32,
}

impl Connection {
    pub(crate) fn new() -> Self {
        let (connection1, connection2) = lsp_server::Connection::memory();

        let server_thread = Some(std::thread::spawn(move || {
            zubanls::run_server_with_custom_connection(connection1, || Ok(()))
                .expect("Should not error");
        }));

        Self {
            client: connection2,
            server_thread,
            request_id_counter: 0,
        }
    }

    pub(crate) fn request<R>(&mut self, params: R::Params) -> R::Result
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
        R::Result: DeserializeOwned,
    {
        self.request_id_counter += 1;
        let id = self.request_id_counter;
        let r = lsp_server::Request::new(id.into(), R::METHOD.to_string(), params);
        self.send(r);

        let response = self.expect_response();
        if let Some(error) = response.error {
            panic!("Unexpected error: {error:?}")
        }
        let value = response.result.expect("Expected result");
        serde_json::from_value(value.clone())
            .unwrap_or_else(|e| panic!("Failed to deserialize {}: {e}; {value}", R::METHOD))
    }

    pub(crate) fn notify<R>(&mut self, params: R::Params)
    where
        R: lsp_types::notification::Notification,
        R::Params: Serialize,
    {
        self.send(lsp_server::Notification::new(R::METHOD.to_string(), params));
    }

    fn send(&mut self, message: impl Into<Message>) {
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
