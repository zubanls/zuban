use std::rc::Rc;
use std::str::FromStr;

use config::ProjectOptions;
use lsp_types::notification::Notification as _;
use lsp_types::request::Request as _;
use vfs::{InMemoryFs, VfsHandler as _};
use wasm_bindgen::prelude::*;
use zuban_python::{Project, RunCause};

use crate::capabilities::{ClientCapabilities, server_capabilities};
use crate::server::{GlobalState, from_json, version};

#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

#[wasm_bindgen]
pub struct ZubanLS {
    state: Option<GlobalState<'static>>,
    fs: InMemoryFs,
    mypy_compat: bool,
}

#[wasm_bindgen]
impl ZubanLS {
    #[wasm_bindgen(constructor)]
    pub fn new(mypy_compat: Option<bool>) -> ZubanLS {
        ZubanLS {
            state: None,
            fs: InMemoryFs::new(),
            mypy_compat: mypy_compat.unwrap_or_default(),
        }
    }

    pub fn set_file(&self, path: &str, contents: &str) {
        self.fs.set_file(path, contents);
    }

    pub fn handle_message(&mut self, msg: &str) -> Option<String> {
        match serde_json::from_str(msg).ok()? {
            lsp_server::Message::Request(req) => {
                Some(serde_json::to_string(&self.dispatch_request(req)).unwrap())
            }
            lsp_server::Message::Notification(notif) => self
                .dispatch_notification(notif)
                .map(|n| serde_json::to_string(&n).unwrap()),
            lsp_server::Message::Response(_) => None,
        }
    }
}

impl ZubanLS {
    fn state(&mut self) -> &mut GlobalState<'static> {
        self.state.as_mut().expect("server uninitialized")
    }

    fn dispatch_request(&mut self, req: lsp_server::Request) -> lsp_server::Response {
        use lsp_types::request::*;
        if req.method == Initialize::METHOD {
            return self.initialize(req);
        }
        macro_rules! dispatch {
            ($($T:ty => $h:ident),* $(,)?) => {
                match req.method.as_str() {
                    $(<$T>::METHOD => {
                        let params = from_json(<$T>::METHOD, &req.params).unwrap();
                        serde_json::to_value(self.state().$h(params).unwrap()).unwrap()
                    })*
                    _ => unreachable!("unknown method: {}", req.method),
                }
            };
        }
        lsp_server::Response::new_ok(
            req.id,
            dispatch! {
                Completion => handle_completion,
                HoverRequest => handle_hover,
                GotoDefinition => handle_goto_definition,
                References => handle_references,
                SignatureHelpRequest => handle_signature_help,
                Rename => rename,
                PrepareRenameRequest => prepare_rename,
                DocumentDiagnosticRequest => handle_document_diagnostics,
                InlayHintRequest => inlay_hints,
                DocumentSymbolRequest => document_symbols,
            },
        )
    }

    fn initialize(&mut self, req: lsp_server::Request) -> lsp_server::Response {
        let params: lsp_types::InitializeParams =
            from_json(lsp_types::request::Initialize::METHOD, &req.params).unwrap();

        let root = params
            .workspace_folders
            .as_ref()
            .and_then(|ws| ws.first())
            .map(|w| w.uri.path().to_string())
            .or_else(|| params.root_uri.as_ref().map(|u| u.path().to_string()))
            .unwrap_or_else(|| "/".into());

        let mut cfg = if self.mypy_compat {
            ProjectOptions::mypy_default()
        } else {
            config::find_workspace_config(&self.fs, &self.fs.unchecked_abs_path(&root), |_| {})
                .unwrap_or_default()
        };
        cfg.settings.typeshed_path = Some(self.fs.normalize_unchecked_abs_path("/typeshed"));

        let project = Project::new(Box::new(self.fs.clone()), cfg, RunCause::LanguageServer);
        let caps = ClientCapabilities::new(params.capabilities);
        self.state = Some(GlobalState::new(caps.clone(), Rc::new([root]), project));

        lsp_server::Response::new_ok(
            req.id,
            lsp_types::InitializeResult {
                capabilities: server_capabilities(&caps),
                server_info: Some(lsp_types::ServerInfo {
                    name: "zuban".into(),
                    version: Some(version().into()),
                }),
                offset_encoding: None,
            },
        )
    }

    fn dispatch_notification(
        &mut self,
        notif: lsp_server::Notification,
    ) -> Option<lsp_server::Notification> {
        use lsp_types::notification::*;
        macro_rules! dispatch {
            ($($T:ty => $h:ident),* $(,)?) => {
                match notif.method.as_str() {
                    $(<$T>::METHOD => {
                        let _ = self.state().$h(from_json(<$T>::METHOD, &notif.params).unwrap());
                    })*
                    _ => {}
                }
            };
        }
        dispatch! {
            DidOpenTextDocument => handle_did_open_text_document,
            DidChangeTextDocument => handle_did_change_text_document,
            DidCloseTextDocument => handle_did_close_text_document,
        }
        match notif.method.as_str() {
            DidOpenTextDocument::METHOD | DidChangeTextDocument::METHOD => {
                let uri = notif.params.get("textDocument")?.get("uri")?.as_str()?;
                self.publish_diagnostics(uri)
            }
            _ => None,
        }
    }

    fn publish_diagnostics(&mut self, uri: &str) -> Option<lsp_server::Notification> {
        let uri = lsp_types::Uri::from_str(uri).ok()?;
        let state = self.state.as_mut()?;
        let encoding = state.client_capabilities.negotiated_encoding();
        let project = state.project();
        let path = GlobalState::uri_to_path(project, &uri).ok()?;
        let document = project.document(&path)?;
        let diagnostics = GlobalState::diagnostics_for_file(document, encoding);
        Some(lsp_server::Notification {
            method: lsp_types::notification::PublishDiagnostics::METHOD.into(),
            params: serde_json::to_value(lsp_types::PublishDiagnosticsParams {
                uri,
                diagnostics,
                version: None,
            })
            .ok()?,
        })
    }
}
