use lsp_types::request::Request;
use serde::{Deserialize, Serialize};

use crate::server::GlobalState;

#[derive(Debug)]
pub enum DisplayStatusRequest {}

impl Request for DisplayStatusRequest {
    type Params = ();
    type Result = DisplayResult;
    const METHOD: &'static str = "zuban/status";
}

#[derive(Debug, PartialEq, Clone, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DisplayResult {
    pub display_version: usize,
    pub zuban_version: String,
    pub zuban_path: String,
    pub type_checking_enabled: bool,
    pub mode: String,
}

impl GlobalState<'_> {
    pub fn display_status(&mut self, _: ()) -> anyhow::Result<DisplayResult> {
        Ok(DisplayResult {
            display_version: 1,
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
        })
    }
}
