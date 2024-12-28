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
        position_encoding: Some(client_capabilities.negotiated_encoding()),
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

#[derive(Debug, PartialEq, Clone, Default)]
pub(crate) struct ClientCapabilities {
    caps: lsp_types::ClientCapabilities,
}

impl ClientCapabilities {
    pub(crate) fn new(caps: lsp_types::ClientCapabilities) -> Self {
        Self { caps }
    }

    pub(crate) fn negotiated_encoding(&self) -> PositionEncodingKind {
        let client_encodings = match &self.caps.general {
            Some(general) => general.position_encodings.as_deref().unwrap_or_default(),
            None => &[],
        };

        for enc in client_encodings {
            if enc == &PositionEncodingKind::UTF8 {
                return PositionEncodingKind::UTF8;
            } else if enc == &PositionEncodingKind::UTF32 {
                return PositionEncodingKind::UTF32;
            }
            // NB: intentionally prefer just about anything else to utf-16.
        }

        PositionEncodingKind::UTF16
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
        let caps = (|| -> _ { self.caps.text_document.as_ref()?.synchronization.clone() })()
            .unwrap_or_default();
        caps.did_save == Some(true) && caps.dynamic_registration == Some(true)
    }

    pub(crate) fn did_change_watched_files_dynamic_registration(&self) -> bool {
        (|| -> _ {
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
        (|| -> _ {
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
        (|| -> _ { self.caps.text_document.as_ref()?.definition?.link_support })()
            .unwrap_or_default()
    }

    pub(crate) fn line_folding_only(&self) -> bool {
        (|| -> _ {
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
        (|| -> _ {
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
        (|| -> _ {
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
        (|| -> _ { self.caps.window.as_ref()?.work_done_progress })().unwrap_or_default()
    }

    pub(crate) fn will_rename(&self) -> bool {
        (|| -> _ {
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
        (|| -> _ {
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
        (|| -> _ {
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
        (|| -> _ {
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

    pub(crate) fn text_document_diagnostic(&self) -> bool {
        (|| -> _ { self.caps.text_document.as_ref()?.diagnostic.as_ref() })().is_some()
    }

    pub(crate) fn text_document_diagnostic_related_document_support(&self) -> bool {
        (|| -> _ {
            self.caps
                .text_document
                .as_ref()?
                .diagnostic
                .as_ref()?
                .related_document_support
        })() == Some(true)
    }

    pub(crate) fn diagnostics_refresh(&self) -> bool {
        (|| -> _ {
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
        (|| -> _ {
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
