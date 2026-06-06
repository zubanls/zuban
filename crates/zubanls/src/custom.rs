use config::IgnoreFileReason;
use lsp_types::{TextDocumentIdentifier, request::Request};
use serde::{Deserialize, Serialize};

use crate::server::GlobalState;

#[derive(Debug)]
pub enum DisplayStatusRequest {}

impl Request for DisplayStatusRequest {
    type Params = TextDocumentIdentifier;
    type Result = DisplayResult;
    const METHOD: &'static str = "zuban/textDocument/status";
}

#[derive(Debug, PartialEq, Clone, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DisplayResult {
    pub version: usize,
    pub zuban_version: String,
    pub zuban_path: String,
    pub type_checking_enabled: bool,
    pub file_errors_ignored_reason: Option<String>,
    pub mode: String,
}

impl GlobalState<'_> {
    pub fn display_status(&mut self, id: TextDocumentIdentifier) -> anyhow::Result<DisplayResult> {
        let document = self.document(&id)?;
        let file_errors_ignored_reason = document.ignored_errors_reason().map(|reason| {
            match reason {
                IgnoreFileReason::IgnoreErrorsInConfigFile => {
                    "The config file has an entry that ignores errors for this file"
                }
                IgnoreFileReason::IgnoreErrorsAtTopOfFile => {
                    "The current file has an entry like `mypy: ignore-errors=True` at the top and therefore ignores errors"
                }
                | IgnoreFileReason::TypeIgnoreAtTopOfFile => {
                    "The current file has an entry like `type: ignore` at the top and therefore ignores errors"
                }
            }
            .into()
        });
        Ok(DisplayResult {
            version: 1,
            zuban_version: env!("CARGO_PKG_VERSION").into(),
            zuban_path: std::env::current_exe()
                .map(|exe| exe.into_os_string().to_string_lossy().into())
                .unwrap_or_else(|_| "<unknown path>".into()),
            type_checking_enabled: self.client_config.type_checking_mode.is_enabled(),
            mode: match self.project().mode() {
                config::Mode::Default => "default",
                config::Mode::Mypy => "mypy",
            }
            .into(),
            file_errors_ignored_reason,
        })
    }
}
