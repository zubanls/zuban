use anyhow::bail;
use config::DiagnosticConfig;
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, FullDocumentDiagnosticReport, Position,
    RelatedFullDocumentDiagnosticReport,
};
use zuban_python::Severity;

use crate::server::{GlobalState, LspError};

impl GlobalState<'_> {
    pub(crate) fn handle_document_diagnostics(
        &mut self,
        params: DocumentDiagnosticParams,
    ) -> anyhow::Result<lsp_types::DocumentDiagnosticReportResult> {
        let path = self.uri_to_path(&params.text_document.uri);
        let project = self.project();
        let Some(mut document) = project.document(path) else {
            tracing::error!("File {path} does not exist");
            bail!(LspError {
                code: lsp_server::ErrorCode::InvalidParams as i32,
                message: format!("File {path} does not exist"),
            });
        };
        let diagnostics = document
            .diagnostics()
            .iter()
            .map(|issue| Diagnostic {
                range: {
                    let to_lsp_position = |pos: zuban_python::FilePosition| {
                        let (line, column) = pos.line_and_column();
                        Position::new(line as u32, column as u32)
                    };
                    lsp_types::Range {
                        start: to_lsp_position(issue.start_position()),
                        end: to_lsp_position(issue.end_position()),
                    }
                },
                severity: Some(match issue.severity() {
                    Severity::Error => DiagnosticSeverity::ERROR,
                    Severity::Warning => DiagnosticSeverity::WARNING,
                    Severity::Information => DiagnosticSeverity::INFORMATION,
                    Severity::Hint => DiagnosticSeverity::HINT,
                }),
                code: Some(lsp_types::NumberOrString::String(
                    issue.mypy_error_code().to_string(),
                )),
                code_description: None,
                source: Some("zubanls".to_owned()),
                message: issue.message(),
                related_information: None,
                tags: None,
                data: None,
            })
            .collect();
        let resp = DocumentDiagnosticReportResult::Report(DocumentDiagnosticReport::Full(
            RelatedFullDocumentDiagnosticReport {
                related_documents: None,
                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items: diagnostics,
                },
            },
        ));
        Ok(resp)
    }

    pub(crate) fn handle_shutdown(&mut self, _: ()) -> anyhow::Result<()> {
        self.shutdown_requested = true;
        Ok(())
    }
}
