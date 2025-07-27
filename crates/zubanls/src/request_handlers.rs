use anyhow::bail;
use lsp_types::{
    Diagnostic, DiagnosticSeverity, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, FullDocumentDiagnosticReport, Hover, HoverContents,
    HoverParams, MarkupContent, MarkupKind, Position, RelatedFullDocumentDiagnosticReport,
    TextDocumentIdentifier, TextDocumentPositionParams,
};
use zuban_python::{Document, InputPosition, PositionInfos, Severity};

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
        let document = self.document(params.text_document)?;
        Ok(DocumentDiagnosticReportResult::Report(
            DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
                related_documents: None,
                full_document_diagnostic_report: FullDocumentDiagnosticReport {
                    result_id: None,
                    items: Self::diagnostics_for_file(document, encoding),
                },
            }),
        ))
    }

    fn to_range(
        encoding: NegotiatedEncoding,
        range: (PositionInfos, PositionInfos),
    ) -> lsp_types::Range {
        let to_lsp_position = |pos: zuban_python::PositionInfos| {
            let column = match encoding {
                NegotiatedEncoding::UTF8 => pos.utf8_bytes_column(),
                NegotiatedEncoding::UTF16 => pos.utf16_code_units_column(),
                NegotiatedEncoding::UTF32 => pos.code_points_column(),
            };
            Position::new(pos.line_zero_based() as u32, column as u32)
        };
        lsp_types::Range {
            start: to_lsp_position(range.0),
            end: to_lsp_position(range.1),
        }
    }

    pub fn diagnostics_for_file(
        mut document: Document,
        encoding: NegotiatedEncoding,
    ) -> Vec<Diagnostic> {
        document
            .diagnostics()
            .iter()
            .map(|issue| Diagnostic {
                range: Self::to_range(encoding, (issue.start_position(), issue.end_position())),
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

    fn document(&mut self, text_document: TextDocumentIdentifier) -> anyhow::Result<Document> {
        let project = self.project();
        let path = Self::uri_to_path(project, text_document.uri)?;
        let Some(document) = project.document(&path) else {
            tracing::error!("File {} does not exist", path.as_uri());
            bail!(LspError {
                code: lsp_server::ErrorCode::InvalidParams as i32,
                message: format!("File {} does not exist", path.as_uri()),
            });
        };
        Ok(document)
    }

    pub fn handle_hover(&mut self, params: HoverParams) -> anyhow::Result<Option<Hover>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params.text_document_position_params)?;

        let Some(documentation_result) = document.documentation(pos)? else {
            return Ok(None);
        };
        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::PlainText,
                value: documentation_result.documentation,
            }),
            range: Some(Self::to_range(
                encoding,
                documentation_result.on_symbol_range,
            )),
        }))
    }

    fn document_with_pos(
        &mut self,
        position: TextDocumentPositionParams,
    ) -> anyhow::Result<(Document, InputPosition)> {
        let line = position.position.line as usize;
        let column = position.position.character as usize;
        let pos = match self.client_capabilities.negotiated_encoding() {
            NegotiatedEncoding::UTF8 => InputPosition::Utf8Bytes { line, column },
            NegotiatedEncoding::UTF16 => InputPosition::Utf16CodeUnits { line, column },
            NegotiatedEncoding::UTF32 => InputPosition::CodePoints { line, column },
        };
        Ok((self.document(position.text_document)?, pos))
    }

    pub(crate) fn handle_shutdown(&mut self, _: ()) -> anyhow::Result<()> {
        self.shutdown_requested = true;
        Ok(())
    }
}
