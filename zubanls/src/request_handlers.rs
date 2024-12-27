use anyhow::bail;
use lsp_server::Message;
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, FullDocumentDiagnosticReport, Position,
    RelatedFullDocumentDiagnosticReport,
};
use zuban_python::{DiagnosticConfig, Severity};

use crate::server::{GlobalState, LspError};

impl GlobalState {
    pub(crate) fn handle_document_diagnostics(
        &mut self,
        params: DocumentDiagnosticParams,
    ) -> anyhow::Result<lsp_types::DocumentDiagnosticReportResult> {
        let project = self.project();
        let path = params.text_document.uri.path().as_str();
        let Some(mut document) = project.document(path) else {
            tracing::error!("File does not exist");
            bail!(LspError {
                code: lsp_server::ErrorCode::InvalidParams as i32,
                message: "File does not exist".into()
            });
        };
        let diagnostics = document
            .diagnostics(&DiagnosticConfig::default())
            .iter()
            .map(|issue| Diagnostic {
                range: {
                    let to_lsp_position = |pos: zuban_python::FilePosition| {
                        let (line, column) = pos.line_and_column();
                        Position::new(line as u32, column as u32)
                    };
                    let start = issue.start_position();
                    let end = issue.end_position();
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
