use anyhow::bail;
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, FullDocumentDiagnosticReport, Position,
    RelatedFullDocumentDiagnosticReport,
};
use zuban_python::{Document, Severity};

use crate::{
    capabilities::NegotiatedEncoding,
    server::{GlobalState, LspError},
};

impl GlobalState<'_> {
    pub(crate) fn handle_document_diagnostics(
        &mut self,
        params: DocumentDiagnosticParams,
    ) -> anyhow::Result<lsp_types::DocumentDiagnosticReportResult> {
        self.sent_diagnostic_count += 1;
        tracing::info!(
            "Requested diagnostics for {} (#{} overall)",
            params.text_document.uri.as_str(),
            self.sent_diagnostic_count
        );
        let encoding = self.client_capabilities.negotiated_encoding();
        let project = self.project();
        let path = Self::uri_to_path(project, params.text_document.uri);
        let Some(mut document) = project.document(&path) else {
            tracing::error!("File {path} does not exist");
            bail!(LspError {
                code: lsp_server::ErrorCode::InvalidParams as i32,
                message: format!("File {path} does not exist"),
            });
        };
        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,
                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items: Self::diagnostics_for_file(&mut document, encoding),
                },
            }),
        ))
    }

    pub fn diagnostics_for_file(
        document: &mut Document,
        encoding: NegotiatedEncoding,
    ) -> Vec<Diagnostic> {
        document
            .diagnostics()
            .iter()
            .map(|issue| Diagnostic {
                range: {
                    let to_lsp_position = |pos: zuban_python::PositionInfos| {
                        let column = match encoding {
                            NegotiatedEncoding::UTF8 => pos.utf8_bytes_column(),
                            NegotiatedEncoding::UTF16 => pos.utf16_code_units_column(),
                            NegotiatedEncoding::UTF32 => pos.code_points_column(),
                        };
                        Position::new(pos.line_zero_based() as u32, column as u32)
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
            .collect()
    }

    pub(crate) fn handle_shutdown(&mut self, _: ()) -> anyhow::Result<()> {
        self.shutdown_requested = true;
        Ok(())
    }
}
