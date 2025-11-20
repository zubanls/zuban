//! Advertises the capabilities of the LSP Server.
use lsp_types::{
    CodeActionProviderCapability, CompletionOptions, DeclarationCapability,
    FoldingRangeProviderCapability, HoverProviderCapability, ImplementationProviderCapability,
    NotebookCellSelector, NotebookDocumentSyncOptions, NotebookSelector, OneOf, Position,
    PositionEncodingKind, RenameOptions, SelectionRangeProviderCapability,
    SemanticTokensFullOptions, SemanticTokensLegend, SemanticTokensOptions,
    SemanticTokensServerCapabilities, ServerCapabilities, SignatureHelpOptions,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TypeDefinitionProviderCapability, WorkspaceFileOperationsServerCapabilities,
    WorkspaceFoldersServerCapabilities, WorkspaceServerCapabilities,
};
use zuban_python::InputPosition;

pub(crate) fn server_capabilities(client_capabilities: &ClientCapabilities) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(client_capabilities.negotiated_encoding().into()),
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::INCREMENTAL),
                will_save: None,
                will_save_wait_until: None,
                save: None, // Currently not needed
            },
        )),
        notebook_document_sync: Some(OneOf::Left(NotebookDocumentSyncOptions {
            notebook_selector: vec![NotebookSelector::ByCells {
                notebook: None,
                cells: vec![NotebookCellSelector {
                    language: "python".into(),
                }],
            }],
            save: None,
        })),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions {
            resolve_provider: Some(true),
            trigger_characters: Some(vec![
                ".".to_owned(),
                "@".to_owned(),
                "(".to_owned(),
                "[".to_owned(),
            ]),
            all_commit_characters: None,
            completion_item: None,
            work_done_progress_options: Default::default(),
        }),
        signature_help_provider: Some(SignatureHelpOptions {
            trigger_characters: Some(vec!["(".to_owned(), ",".to_owned(), ")".to_owned()]),
            retrigger_characters: None,
            work_done_progress_options: Default::default(),
        }),
        declaration_provider: Some(DeclarationCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
        implementation_provider: Some(ImplementationProviderCapability::Simple(true)),
        references_provider: Some(OneOf::Left(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        workspace_symbol_provider: Some(OneOf::Left(true)),
        code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
        code_lens_provider: None,
        document_formatting_provider: None,       // TODO
        document_range_formatting_provider: None, // TODO
        document_on_type_formatting_provider: None,
        selection_range_provider: Some(SelectionRangeProviderCapability::Simple(true)),
        folding_range_provider: Some(FoldingRangeProviderCapability::Simple(true)),
        rename_provider: Some(OneOf::Right(RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: Default::default(),
        })),
        linked_editing_range_provider: None,
        document_link_provider: None,
        color_provider: None,
        execute_command_provider: None,
        workspace: Some(WorkspaceServerCapabilities {
            workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                supported: Some(true),
                change_notifications: Some(OneOf::Left(true)),
            }),
            file_operations: Some(WorkspaceFileOperationsServerCapabilities {
                did_create: None,
                will_create: None,
                did_rename: None,
                will_rename: None,
                did_delete: None,
                will_delete: None,
            }),
        }),
        call_hierarchy_provider: None, // TODO
        semantic_tokens_provider: Some(SemanticTokensServerCapabilities::SemanticTokensOptions(
            SemanticTokensOptions {
                work_done_progress_options: Default::default(),
                legend: SemanticTokensLegend {
                    token_types: crate::semantic_tokens::SUPPORTED_TYPES.to_vec(),
                    token_modifiers: crate::semantic_tokens::SUPPORTED_MODIFIERS.to_vec(),
                },
                range: Some(true),
                full: Some(SemanticTokensFullOptions::Bool(true)),
            },
        )),
        moniker_provider: None,
        inlay_hint_provider: None, // TODO
        inline_value_provider: None,
        experimental: None,
        diagnostic_provider: Some(lsp_types::DiagnosticServerCapabilities::Options(
            lsp_types::DiagnosticOptions {
                identifier: None,
                inter_file_dependencies: true,
                // FIXME
                workspace_diagnostics: false,
                work_done_progress_options: Default::default(),
            },
        )),
        inline_completion_provider: None,
    }
}

#[derive(Debug, PartialEq, Clone)]
pub(crate) struct ClientCapabilities {
    caps: lsp_types::ClientCapabilities,
    negotiated_encoding: NegotiatedEncoding,
    should_push_diagnostics: bool,
}

impl ClientCapabilities {
    pub(crate) fn new(caps: lsp_types::ClientCapabilities) -> Self {
        let negotiated_encoding = Self::negotiate_encoding(&caps);
        tracing::info!("Negotiated encoding to {negotiated_encoding:?}");
        let should_push_diagnostics = !Self::text_document_diagnostic(&caps);
        Self {
            caps,
            negotiated_encoding,
            should_push_diagnostics,
        }
    }

    fn negotiate_encoding(caps: &lsp_types::ClientCapabilities) -> NegotiatedEncoding {
        let client_encodings = match &caps.general {
            Some(general) => general.position_encodings.as_deref().unwrap_or_default(),
            None => &[],
        };

        for enc in client_encodings {
            if enc == &PositionEncodingKind::UTF8 {
                return NegotiatedEncoding::UTF8;
            } else if enc == &PositionEncodingKind::UTF32 {
                return NegotiatedEncoding::UTF32;
            }
            // NB: intentionally prefer just about anything else to utf-16.
        }

        NegotiatedEncoding::UTF16
    }

    pub fn negotiated_encoding(&self) -> NegotiatedEncoding {
        self.negotiated_encoding
    }

    pub(crate) fn workspace_edit_resource_operations(
        &self,
    ) -> Option<&[lsp_types::ResourceOperationKind]> {
        self.caps
            .workspace
            .as_ref()?
            .workspace_edit
            .as_ref()?
            .resource_operations
            .as_deref()
    }

    pub(crate) fn location_link(&self) -> bool {
        (|| self.caps.text_document.as_ref()?.definition?.link_support)().unwrap_or_default()
    }

    pub(crate) fn line_folding_only(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .folding_range
                .as_ref()?
                .line_folding_only
        })()
        .unwrap_or_default()
    }

    pub(crate) fn hierarchical_symbols(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .document_symbol
                .as_ref()?
                .hierarchical_document_symbol_support
        })()
        .unwrap_or_default()
    }

    #[expect(dead_code)]
    pub(crate) fn code_action_literals(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .code_action
                .as_ref()?
                .code_action_literal_support
                .as_ref()
        })()
        .is_some()
    }

    #[expect(dead_code)]
    pub(crate) fn code_action_resolve(&self) -> bool {
        (|| {
            Some(
                self.caps
                    .text_document
                    .as_ref()?
                    .code_action
                    .as_ref()?
                    .resolve_support
                    .as_ref()?
                    .properties
                    .as_slice(),
            )
        })()
        .unwrap_or_default()
        .iter()
        .any(|it| it == "edit")
    }

    pub(crate) fn signature_help_label_offsets(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .signature_help
                .as_ref()?
                .signature_information
                .as_ref()?
                .parameter_information
                .as_ref()?
                .label_offset_support
        })()
        .unwrap_or_default()
    }

    fn text_document_diagnostic(caps: &lsp_types::ClientCapabilities) -> bool {
        (|| caps.text_document.as_ref()?.diagnostic.as_ref())().is_some()
    }

    pub fn should_push_diagnostics(&self) -> bool {
        self.should_push_diagnostics
    }

    #[expect(dead_code)]
    pub(crate) fn diagnostics_refresh(&self) -> bool {
        (|| {
            self.caps
                .workspace
                .as_ref()?
                .diagnostic
                .as_ref()?
                .refresh_support
        })()
        .unwrap_or_default()
    }

    #[expect(dead_code)]
    pub(crate) fn insert_replace_support(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .completion
                .as_ref()?
                .completion_item
                .as_ref()?
                .insert_replace_support
        })()
        .unwrap_or_default()
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub(crate) enum NegotiatedEncoding {
    UTF8,
    UTF16,
    UTF32,
}

impl From<NegotiatedEncoding> for PositionEncodingKind {
    fn from(value: NegotiatedEncoding) -> Self {
        match value {
            NegotiatedEncoding::UTF8 => PositionEncodingKind::UTF8,
            NegotiatedEncoding::UTF16 => PositionEncodingKind::UTF16,
            NegotiatedEncoding::UTF32 => PositionEncodingKind::UTF32,
        }
    }
}

impl NegotiatedEncoding {
    pub fn input_position(&self, position: Position) -> InputPosition {
        let line = position.line as usize;
        let column = position.character as usize;
        match self {
            Self::UTF8 => InputPosition::Utf8Bytes { line, column },
            Self::UTF16 => InputPosition::Utf16CodeUnits { line, column },
            Self::UTF32 => InputPosition::CodePoints { line, column },
        }
    }
}
