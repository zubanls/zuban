use std::{collections::HashMap, str::FromStr};

use anyhow::bail;
use lsp_server::ErrorCode;
use lsp_types::{
    CodeAction, CodeActionKind, CodeActionOrCommand, CodeActionParams, CodeActionResponse,
    CompletionItem, CompletionParams, CompletionResponse, CompletionTextEdit, Diagnostic,
    DiagnosticSeverity, DocumentChangeOperation, DocumentChanges, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, DocumentHighlight,
    DocumentHighlightKind, DocumentHighlightParams, DocumentSymbol, DocumentSymbolParams,
    DocumentSymbolResponse, FullDocumentDiagnosticReport, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverContents, HoverParams, Location, LocationLink,
    MarkupContent, MarkupKind, OneOf, OptionalVersionedTextDocumentIdentifier,
    ParameterInformation, ParameterLabel, Position, PrepareRenameResponse, Range, ReferenceParams,
    RelatedFullDocumentDiagnosticReport, RenameFile, RenameParams, ResourceOp,
    ResourceOperationKind, SelectionRange, SelectionRangeParams, SemanticTokens,
    SemanticTokensParams, SemanticTokensRangeParams, SemanticTokensRangeResult,
    SemanticTokensResult, SignatureHelp, SignatureHelpParams, SignatureInformation, SymbolKind,
    TextDocumentEdit, TextDocumentIdentifier, TextDocumentPositionParams, TextEdit, Uri,
    WorkspaceEdit, WorkspaceSymbol, WorkspaceSymbolParams, WorkspaceSymbolResponse,
    request::{
        GotoDeclarationParams, GotoDeclarationResponse, GotoImplementationParams,
        GotoImplementationResponse, GotoTypeDefinitionParams, GotoTypeDefinitionResponse,
    },
};
use rayon::prelude::*;
use zuban_python::{
    Document, GotoGoal, InputPosition, Name, NameSymbol, PositionInfos, ReferencesGoal, Severity,
};

use crate::{
    capabilities::{ClientCapabilities, NegotiatedEncoding},
    semantic_tokens::SemanticTokensBuilder,
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

    fn to_position(encoding: NegotiatedEncoding, pos: PositionInfos) -> lsp_types::Position {
        let column = match encoding {
            NegotiatedEncoding::UTF8 => pos.utf8_bytes_column(),
            NegotiatedEncoding::UTF16 => pos.utf16_code_units_column(),
            NegotiatedEncoding::UTF32 => pos.code_points_column(),
        };
        Position::new(pos.line_zero_based() as u32, column as u32)
    }

    fn to_range(
        encoding: NegotiatedEncoding,
        range: (PositionInfos, PositionInfos),
    ) -> lsp_types::Range {
        lsp_types::Range {
            start: Self::to_position(encoding, range.0),
            end: Self::to_position(encoding, range.1),
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

    fn document(&mut self, text_document: TextDocumentIdentifier) -> anyhow::Result<Document<'_>> {
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

    pub fn handle_completion(
        &mut self,
        params: CompletionParams,
    ) -> anyhow::Result<Option<CompletionResponse>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params.text_document_position)?;
        let mut completions = document.complete(pos, false, |replace_range, completion| {
            CompletionItem {
                label: completion.label().to_string(),
                kind: Some(completion.kind()),
                text_edit: Some(CompletionTextEdit::Edit(TextEdit {
                    range: Self::to_range(encoding, replace_range),
                    new_text: completion.insert_text(),
                })),
                // TODO
                // documentation: Some(Documentation::String(completion.documentation().unwrap_or_else())),
                ..Default::default()
            }
        })?;
        tracing::trace!("Completion results: {completions:?}");
        if completions.is_empty() {
            return Ok(None);
        }
        // Completions are already sorted. Make sure the client does not reorder them.
        for (i, c) in completions.iter_mut().enumerate() {
            c.sort_text = Some(format!("{i:05x}"));
        }

        Ok(Some(CompletionResponse::Array(completions)))
    }

    pub fn handle_signature_help(
        &mut self,
        params: SignatureHelpParams,
    ) -> anyhow::Result<Option<SignatureHelp>> {
        let _p = tracing::info_span!("handle_signature_help").entered();
        let signature_help_label_offsets = self.client_capabilities.signature_help_label_offsets();
        let (document, pos) = self.document_with_pos(params.text_document_position_params)?;
        let signatures = document.call_signatures(pos)?;
        let mut first_active_signature = None;
        let mut first_active_parameter = None;
        Ok(signatures.map(|signatures| SignatureHelp {
            signatures: signatures
                .into_iterator()
                .enumerate()
                .map(|(i, sig)| {
                    let active_parameter = sig.current_param.map(|active| active as u32);
                    if sig.is_valid_with_arguments && first_active_signature.is_none() {
                        first_active_signature = Some(i as u32);
                        first_active_parameter = active_parameter;
                    }
                    SignatureInformation {
                        parameters: sig.params().map(|params| {
                            params
                                .map(|p| ParameterInformation {
                                    label: if signature_help_label_offsets {
                                        let range = p.utf16_code_units_name_range();
                                        ParameterLabel::LabelOffsets([
                                            range.0 as u32,
                                            range.1 as u32,
                                        ])
                                    } else {
                                        ParameterLabel::Simple(p.name().to_string())
                                    },
                                    documentation: None,
                                })
                                .collect()
                        }),
                        label: sig.label.into_string(),
                        documentation: None,
                        active_parameter,
                    }
                })
                .collect(),
            active_signature: first_active_signature,
            active_parameter: first_active_parameter,
        }))
    }

    pub fn handle_hover(&mut self, params: HoverParams) -> anyhow::Result<Option<Hover>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params.text_document_position_params)?;

        let Some(documentation_result) = document.documentation(pos, false)? else {
            return Ok(None);
        };
        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: documentation_result.documentation,
            }),
            range: Some(Self::to_range(
                encoding,
                documentation_result.on_symbol_range,
            )),
        }))
    }

    pub fn handle_goto_declaration(
        &mut self,
        params: GotoDeclarationParams,
    ) -> anyhow::Result<Option<GotoDeclarationResponse>> {
        self.run_goto_like(
            params,
            |document, pos, on_result| document.goto(pos, GotoGoal::Indifferent, false, on_result),
            |document, pos, on_result| document.goto(pos, GotoGoal::Indifferent, false, on_result),
        )
    }

    pub fn handle_goto_definition(
        &mut self,
        params: GotoDefinitionParams,
    ) -> anyhow::Result<Option<GotoDefinitionResponse>> {
        self.run_goto_like(
            params,
            |document, pos, on_result| {
                document.goto(pos, GotoGoal::PreferNonStubs, true, on_result)
            },
            |document, pos, on_result| {
                document.goto(pos, GotoGoal::PreferNonStubs, true, on_result)
            },
        )
    }

    pub fn handle_goto_implementation(
        &mut self,
        params: GotoImplementationParams,
    ) -> anyhow::Result<Option<GotoImplementationResponse>> {
        self.run_goto_like(
            params,
            |document, pos, on_result| {
                document.infer_definition(pos, GotoGoal::PreferNonStubs, |vn| on_result(vn.name))
            },
            |document, pos, on_result| {
                document.infer_definition(pos, GotoGoal::PreferNonStubs, |vn| on_result(vn.name))
            },
        )
    }

    pub fn handle_goto_type_definition(
        &mut self,
        params: GotoTypeDefinitionParams,
    ) -> anyhow::Result<Option<GotoTypeDefinitionResponse>> {
        self.run_goto_like(
            params,
            |document, pos, on_result| document.goto(pos, GotoGoal::PreferStubs, true, on_result),
            |document, pos, on_result| document.goto(pos, GotoGoal::PreferStubs, true, on_result),
        )
    }

    fn run_goto_like(
        &mut self,
        params: GotoDefinitionParams,
        run_for_location: impl FnOnce(
            Document,
            InputPosition,
            &dyn Fn(Name) -> Location,
        ) -> anyhow::Result<Vec<Location>>,
        // We don't have rank-2 polymorphism over types
        run_for_location_link: impl FnOnce(
            Document,
            InputPosition,
            &dyn Fn(Name) -> LocationLink,
        ) -> anyhow::Result<Vec<LocationLink>>,
    ) -> anyhow::Result<Option<GotoDefinitionResponse>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let has_location_link_support = self.client_capabilities.location_link();
        let (document, pos) = self.document_with_pos(params.text_document_position_params)?;
        let response = if has_location_link_support {
            let result = run_for_location(document, pos, &|name| lsp_location(encoding, name))?;
            if result.is_empty() {
                return Ok(None);
            }
            result.into()
        } else {
            let result = run_for_location_link(document, pos, &|name| LocationLink {
                target_uri: Uri::from_str(&name.file_uri()).expect("Expected a valid URI"),
                target_range: Self::to_range(encoding, name.target_range()),
                origin_selection_range: None,
                target_selection_range: Self::to_range(encoding, name.name_range()),
            })?;
            if result.is_empty() {
                return Ok(None);
            }
            result.into()
        };
        Ok(Some(response))
    }

    fn document_with_pos(
        &mut self,
        text_position: TextDocumentPositionParams,
    ) -> anyhow::Result<(Document<'_>, InputPosition)> {
        let pos = self
            .client_capabilities
            .negotiated_encoding()
            .input_position(text_position.position);
        Ok((self.document(text_position.text_document)?, pos))
    }

    pub fn handle_references(
        &mut self,
        params: ReferenceParams,
    ) -> anyhow::Result<Option<Vec<Location>>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params.text_document_position)?;
        let result = document.references(
            pos,
            ReferencesGoal::OnlyTypeCheckedWorkspaces,
            params.context.include_declaration,
            |name| {
                Location::new(
                    Uri::from_str(&name.file_uri()).expect("Expected a valid URI"),
                    Self::to_range(encoding, name.name_range()),
                )
            },
        )?;
        if result.is_empty() {
            return Ok(None);
        }
        Ok(Some(result))
    }

    pub fn handle_document_highlight(
        &mut self,
        params: DocumentHighlightParams,
    ) -> anyhow::Result<Option<Vec<DocumentHighlight>>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params.text_document_position_params)?;
        let result = document.references(pos, ReferencesGoal::OnlyCurrentFile, true, |name| {
            DocumentHighlight {
                range: Self::to_range(encoding, name.name_range()),
                kind: Some(match name.is_definition() {
                    true => DocumentHighlightKind::WRITE,
                    false => DocumentHighlightKind::READ,
                }),
            }
        })?;
        if result.is_empty() {
            return Ok(None);
        }
        Ok(Some(result))
    }

    pub fn code_actions(
        &mut self,
        params: CodeActionParams,
    ) -> anyhow::Result<Option<CodeActionResponse>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let uri = params.text_document.uri.clone();
        let document = self.document(params.text_document)?;
        let actions = document.code_actions(
            encoding.input_position(params.range.start),
            Some(encoding.input_position(params.range.end)),
        )?;
        if actions.is_empty() {
            return Ok(None);
        }
        Ok(Some(
            actions
                .into_iter()
                .map(|action| {
                    CodeActionOrCommand::CodeAction(CodeAction {
                        title: action.title,
                        kind: Some(CodeActionKind::QUICKFIX),
                        diagnostics: None,
                        edit: Some(WorkspaceEdit::new(HashMap::from_iter([(
                            uri.clone(),
                            vec![TextEdit {
                                range: Self::to_range(
                                    encoding,
                                    (action.start_of_change, action.end_of_change),
                                ),
                                new_text: action.replacement,
                            }],
                        )]))),
                        command: None,
                        is_preferred: None,
                        disabled: None,
                        data: None,
                    })
                })
                .collect(),
        ))
    }

    pub fn prepare_rename(
        &mut self,
        params: TextDocumentPositionParams,
    ) -> anyhow::Result<Option<PrepareRenameResponse>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let (document, pos) = self.document_with_pos(params)?;
        let range = document.is_valid_rename_location(pos)?;
        if let Some((start, end)) = range {
            Ok(Some(PrepareRenameResponse::Range(Self::to_range(
                encoding,
                (start, end),
            ))))
        } else {
            Ok(None)
        }
    }

    pub fn rename(&mut self, params: RenameParams) -> anyhow::Result<Option<WorkspaceEdit>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let new_name = params.new_name;
        let (document, pos) = self.document_with_pos(params.text_document_position)?;
        let mut changes = document.references_for_rename(pos, &new_name)?;
        Ok(if changes.has_changes() {
            let workspace_changes: Vec<_> = std::mem::take(&mut changes.changes)
                .into_iter()
                .map(|change| {
                    DocumentChangeOperation::Edit(TextDocumentEdit {
                        text_document: OptionalVersionedTextDocumentIdentifier {
                            uri: to_uri(change.path.as_uri()),
                            version: None,
                        },
                        edits: change
                            .ranges
                            .into_iter()
                            .map(|range| {
                                OneOf::Left(TextEdit {
                                    range: Self::to_range(encoding, range),
                                    new_text: new_name.clone(),
                                })
                            })
                            .collect(),
                    })
                })
                .chain(changes.renames().map(|rename| {
                    DocumentChangeOperation::Op(ResourceOp::Rename(RenameFile {
                        old_uri: to_uri(rename.from_uri()),
                        new_uri: to_uri(rename.to_uri()),
                        options: None,
                        annotation_id: None,
                    }))
                }))
                .collect();
            let edit = WorkspaceEdit {
                changes: None,
                document_changes: Some(DocumentChanges::Operations(workspace_changes)),
                change_annotations: None,
            };
            ensure_valid_workspace_edit(&self.client_capabilities, &edit)?;
            Some(edit)
        } else {
            None
        })
    }

    pub fn document_symbols(
        &mut self,
        params: DocumentSymbolParams,
    ) -> anyhow::Result<Option<DocumentSymbolResponse>> {
        tracing::info!(
            "Requested document symbols for {}",
            params.text_document.uri.as_str(),
        );
        let encoding = self.client_capabilities.negotiated_encoding();
        let hierarchical_symbols = self.client_capabilities.hierarchical_symbols();
        if !hierarchical_symbols {
            // This is not supported for now, VSCode supports doesn't do it that way and until I
            // find a client that does I won't implement it.
            return Ok(None);
        }

        let document = self.document(params.text_document)?;
        Ok(Some(DocumentSymbolResponse::Nested(
            Self::nested_doc_symbols(encoding, document.symbols()),
        )))
    }

    fn nested_doc_symbols<'x>(
        encoding: NegotiatedEncoding,
        symbols: impl Iterator<Item = NameSymbol<'x>>,
    ) -> Vec<DocumentSymbol> {
        symbols
            .map(|symbol| {
                let name = symbol.as_name();
                let kind = name.lsp_kind();
                let children = if kind == SymbolKind::CLASS {
                    name.class_symbols()
                        .map(|sym| Self::nested_doc_symbols(encoding, sym))
                } else {
                    None
                };
                #[expect(deprecated)]
                DocumentSymbol {
                    name: symbol.symbol.into(),
                    detail: name.simple_qualified_name_of_parent_without_file(),
                    kind,
                    tags: None,
                    deprecated: None,
                    range: Self::to_range(encoding, name.target_range()),
                    selection_range: Self::to_range(encoding, name.name_range()),
                    children,
                }
            })
            .collect()
    }

    fn nested_workspace_doc_symbols<'x>(
        encoding: NegotiatedEncoding,
        symbols: impl Iterator<Item = NameSymbol<'x>>,
        query: &str,
        add: &mut impl FnMut(WorkspaceSymbol),
    ) {
        for symbol in symbols {
            if symbol.symbol.contains(query) {
                let name = symbol.as_name();
                let kind = name.lsp_kind();
                if kind == SymbolKind::CLASS
                    && let Some(child_symbols) = name.class_symbols()
                {
                    Self::nested_workspace_doc_symbols(encoding, child_symbols, query, add);
                }
                add(WorkspaceSymbol {
                    name: symbol.symbol.into(),
                    kind,
                    tags: None,
                    container_name: name.simple_qualified_name_of_parent_without_file(),
                    location: OneOf::Left(lsp_location(encoding, name)),
                    data: None,
                });
            }
        }
    }

    pub fn workspace_symbols(
        &mut self,
        params: WorkspaceSymbolParams,
    ) -> anyhow::Result<Option<WorkspaceSymbolResponse>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let symbols = self
            .project()
            .workspace_documents()
            .map(|doc| {
                let symbols = doc.symbols();
                let mut out = Vec::with_capacity(symbols.len());
                Self::nested_workspace_doc_symbols(encoding, symbols, &params.query, &mut |s| {
                    out.push(s)
                });
                out
            })
            .flatten_iter()
            .collect();
        Ok(Some(WorkspaceSymbolResponse::Nested(symbols)))
    }

    pub fn semantic_tokens(
        &mut self,
        params: SemanticTokensParams,
    ) -> anyhow::Result<Option<SemanticTokensResult>> {
        Ok(Some(SemanticTokensResult::Tokens(
            self.semantic_tokens_internal(params.text_document, None)?,
        )))
    }

    fn semantic_tokens_internal(
        &mut self,
        document: TextDocumentIdentifier,
        range: Option<Range>,
    ) -> anyhow::Result<SemanticTokens> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let document = self.document(document)?;
        let mut builder = SemanticTokensBuilder::new();
        let range = range.map(|range| {
            (
                encoding.input_position(range.start),
                encoding.input_position(range.end),
            )
        });
        for semantic_token in document.semantic_tokens(range)? {
            builder.push(
                Self::to_position(encoding, semantic_token.position()),
                semantic_token.length(),
                semantic_token.lsp_type,
                semantic_token.properties,
            );
        }
        Ok(builder.build())
    }

    pub fn semantic_tokens_with_range(
        &mut self,
        params: SemanticTokensRangeParams,
    ) -> anyhow::Result<Option<SemanticTokensRangeResult>> {
        Ok(Some(SemanticTokensRangeResult::Tokens(
            self.semantic_tokens_internal(params.text_document, Some(params.range))?,
        )))
    }

    pub fn selection_ranges(
        &mut self,
        params: SelectionRangeParams,
    ) -> anyhow::Result<Option<Vec<SelectionRange>>> {
        let encoding = self.client_capabilities.negotiated_encoding();
        let document = self.document(params.text_document)?;
        fn range_iterator_to_selection_range<'x>(
            encoding: NegotiatedEncoding,
            mut ranges: impl Iterator<Item = (PositionInfos<'x>, PositionInfos<'x>)>,
        ) -> Option<SelectionRange> {
            let next_range = ranges.next()?;
            Some(SelectionRange {
                range: GlobalState::to_range(encoding, next_range),
                parent: range_iterator_to_selection_range(encoding, ranges).map(Box::new),
            })
        }
        Ok(Some(
            params
                .positions
                .into_iter()
                .map(|pos| {
                    Ok(range_iterator_to_selection_range(
                        encoding,
                        document.selection_ranges(encoding.input_position(pos))?,
                    )
                    .unwrap())
                })
                .collect::<anyhow::Result<_>>()?,
        ))
    }

    pub(crate) fn handle_shutdown(&mut self, _: ()) -> anyhow::Result<()> {
        self.shutdown_requested = true;
        Ok(())
    }
}

fn ensure_valid_workspace_edit(
    cap: &ClientCapabilities,
    edit: &WorkspaceEdit,
) -> anyhow::Result<()> {
    if let Some(lsp_types::DocumentChanges::Operations(ops)) = edit.document_changes.as_ref() {
        for op in ops {
            if let lsp_types::DocumentChangeOperation::Op(doc_change_op) = op {
                resource_ops_supported(cap, resolve_resource_op(doc_change_op))?
            }
        }
    }
    Ok(())
}

fn to_uri(s: String) -> Uri {
    Uri::from_str(&s)
        .unwrap_or_else(|err| panic!("Tried to parse the URI {s}, but failed with {err:?}"))
}

fn resolve_resource_op(op: &ResourceOp) -> ResourceOperationKind {
    match op {
        ResourceOp::Create(_) => ResourceOperationKind::Create,
        ResourceOp::Rename(_) => ResourceOperationKind::Rename,
        ResourceOp::Delete(_) => ResourceOperationKind::Delete,
    }
}

fn resource_ops_supported(
    cap: &ClientCapabilities,
    kind: ResourceOperationKind,
) -> anyhow::Result<()> {
    if !matches!(cap.workspace_edit_resource_operations(), Some(resops) if resops.contains(&kind)) {
        return Err(LspError {
            code: ErrorCode::RequestFailed as i32,
            message: format!(
                "Client does not support {} capability.",
                match kind {
                    ResourceOperationKind::Create => "create",
                    ResourceOperationKind::Rename => "rename",
                    ResourceOperationKind::Delete => "delete",
                }
            ),
        }
        .into());
    }

    Ok(())
}

fn lsp_location(encoding: NegotiatedEncoding, name: Name) -> Location {
    Location::new(
        Uri::from_str(&name.file_uri()).expect("Expected a valid URI"),
        GlobalState::to_range(encoding, name.name_range()),
    )
}
