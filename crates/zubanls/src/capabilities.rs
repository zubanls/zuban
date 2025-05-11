#![allow(unused)] // TODO remove, there are currently quite a few unused methods

//! Advertises the capabilities of the LSP Server.
use lsp_types::{
    OneOf, PositionEncodingKind, ServerCapabilities, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, WorkDoneProgressOptions,
    WorkspaceFileOperationsServerCapabilities, WorkspaceFoldersServerCapabilities,
    WorkspaceServerCapabilities,
};

pub(crate) fn server_capabilities(client_capabilities: &ClientCapabilities) -> ServerCapabilities {
    ServerCapabilities {
        position_encoding: Some(client_capabilities.negotiated_encoding().into()),
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::FULL),
                will_save: None,
                will_save_wait_until: None,
                save: None, // Currently not needed
            },
        )),
        workspace: Some(WorkspaceServerCapabilities {
            workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                supported: Some(true),
                change_notifications: Some(OneOf::Left(true)),
            }),
            file_operations: Some(WorkspaceFileOperationsServerCapabilities {
                did_create: None,
                will_create: None,
                did_rename: None,
                // TODO do we need this?
                will_rename: None,
                did_delete: None,
                will_delete: None,
            }),
        }),
        diagnostic_provider: Some(lsp_types::DiagnosticServerCapabilities::Options(
            lsp_types::DiagnosticOptions {
                identifier: None,
                inter_file_dependencies: true,
                // FIXME
                workspace_diagnostics: false,
                work_done_progress_options: WorkDoneProgressOptions {
                    work_done_progress: None,
                },
            },
        )),
        ..Default::default()
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
        let should_push_diagnostics = Self::text_document_diagnostic(&caps);
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

    pub(crate) fn did_save_text_document_dynamic_registration(&self) -> bool {
        let caps =
            (|| self.caps.text_document.as_ref()?.synchronization.clone())().unwrap_or_default();
        caps.did_save == Some(true) && caps.dynamic_registration == Some(true)
    }

    pub(crate) fn did_change_watched_files_dynamic_registration(&self) -> bool {
        (|| {
            self.caps
                .workspace
                .as_ref()?
                .did_change_watched_files
                .as_ref()?
                .dynamic_registration
        })()
        .unwrap_or_default()
    }

    pub(crate) fn did_change_watched_files_relative_pattern_support(&self) -> bool {
        (|| {
            self.caps
                .workspace
                .as_ref()?
                .did_change_watched_files
                .as_ref()?
                .relative_pattern_support
        })()
        .unwrap_or_default()
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

    pub(crate) fn work_done_progress(&self) -> bool {
        (|| self.caps.window.as_ref()?.work_done_progress)().unwrap_or_default()
    }

    pub(crate) fn will_rename(&self) -> bool {
        (|| {
            self.caps
                .workspace
                .as_ref()?
                .file_operations
                .as_ref()?
                .will_rename
        })()
        .unwrap_or_default()
    }

    pub(crate) fn change_annotation_support(&self) -> bool {
        (|| {
            self.caps
                .workspace
                .as_ref()?
                .workspace_edit
                .as_ref()?
                .change_annotation_support
                .as_ref()
        })()
        .is_some()
    }

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

    pub(crate) fn text_document_diagnostic_related_document_support(&self) -> bool {
        (|| {
            self.caps
                .text_document
                .as_ref()?
                .diagnostic
                .as_ref()?
                .related_document_support
        })() == Some(true)
    }

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
