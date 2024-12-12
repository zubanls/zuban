use lsp_server::ErrorCode;
use lsp_types::{notification::PublishDiagnostics, PublishDiagnosticsParams, Uri};

use crate::server::client::Notifier;
use crate::server::Result;

use super::LSPResult;

pub(super) fn clear_diagnostics(uri: &Uri, notifier: &Notifier) -> Result<()> {
    notifier
        .notify::<PublishDiagnostics>(PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: vec![],
            version: None,
        })
        .with_failure_code(ErrorCode::InternalError)?;
    Ok(())
}
