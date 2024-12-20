//! The most high-level integrated tests for ZubanLS (copied from rust-analyzer).
//!
//! This tests run a full LSP event loop. For this reason, the tests here are very slow, and should
//! be avoided unless absolutely necessary.
//!
//! In particular, it's fine *not* to test that client & server agree on
//! specific JSON shapes here -- there's little value in such tests, as we can't
//! be sure without a real client anyway.

use std::str::FromStr;

use lsp_types::{DiagnosticServerCapabilities, PositionEncodingKind, Uri};

mod connection;

use connection::Connection;

#[test]
fn basic_server_setup() {
    let mut con = Connection::new();

    #[expect(deprecated)]
    let initialize_params = lsp_types::InitializeParams {
        root_uri: Some(Uri::from_str("file:///foo/bar").unwrap()),
        capabilities: lsp_types::ClientCapabilities {
            workspace: Some(lsp_types::WorkspaceClientCapabilities {
                did_change_watched_files: Some(
                    lsp_types::DidChangeWatchedFilesClientCapabilities {
                        dynamic_registration: Some(true),
                        relative_pattern_support: None,
                    },
                ),
                workspace_edit: Some(lsp_types::WorkspaceEditClientCapabilities {
                    resource_operations: Some(vec![
                        lsp_types::ResourceOperationKind::Create,
                        lsp_types::ResourceOperationKind::Delete,
                        lsp_types::ResourceOperationKind::Rename,
                    ]),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            ..Default::default()
        },
        ..Default::default()
    };
    let response = con.request::<lsp_types::request::Initialize>(initialize_params);
    // Check diagnostic capabilities
    {
        assert_eq!(
            response
                .capabilities
                .position_encoding
                .expect("position_encoding"),
            PositionEncodingKind::UTF16
        );
        let Some(DiagnosticServerCapabilities::Options(diagnostics)) =
            response.capabilities.diagnostic_provider
        else {
            unreachable!()
        };
        assert!(diagnostics.inter_file_dependencies);
        // For now this is false, but this might change
        assert!(!diagnostics.workspace_diagnostics);
    }
    assert_eq!(response.server_info.expect("server_info").name, "zubanls");

    con.notify::<lsp_types::notification::Initialized>(lsp_types::InitializedParams {});
    con.notify::<lsp_types::notification::Exit>(());
}
