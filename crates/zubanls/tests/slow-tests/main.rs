//! The most high-level integrated tests for ZubanLS (copied from rust-analyzer).
//!
//! This tests run a full LSP event loop. For this reason, the tests here are very slow, and should
//! be avoided unless absolutely necessary.
//!
//! In particular, it's fine *not* to test that client & server agree on
//! specific JSON shapes here -- there's little value in such tests, as we can't
//! be sure without a real client anyway.

use std::str::FromStr;

use lsp_server::Response;
use lsp_types::{
    notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument},
    request::DocumentDiagnosticRequest,
    DiagnosticServerCapabilities, DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, NumberOrString, PartialResultParams, PositionEncodingKind,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, Uri,
    VersionedTextDocumentIdentifier, WorkDoneProgressParams,
};

mod connection;
mod support;
mod testdir;

use connection::Connection;
use serde_json::json;
use support::Project;

#[test]
fn basic_server_setup() {
    let con = Connection::new();
    let response = con.initialize(&["/foo/bar"]);

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
    con.shutdown_and_exit()
}

#[test]
fn request_after_shutdown_is_invalid() {
    let con = Connection::initialized(&["/foo/bar"]);
    con.request::<lsp_types::request::Shutdown>(());

    let expect_shutdown_already_requested = |response: Response| {
        let error = response.error.unwrap();
        assert_eq!(error.message, "Shutdown already requested.");
        assert_eq!(error.code, lsp_server::ErrorCode::InvalidRequest as i32);
        assert!(response.result.is_none());
    };

    // Invalid, because there was already a shutdown request.
    let r = con.request_with_response::<lsp_types::request::Shutdown>(());
    expect_shutdown_already_requested(r);

    let r = con.request_with_response::<lsp_types::request::DocumentDiagnosticRequest>(
        DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier::new(Uri::from_str("does-not-exist").unwrap()),
            identifier: None,
            previous_result_id: None,
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        },
    );
    expect_shutdown_already_requested(r);

    // This is ok.
    con.notify::<lsp_types::notification::Exit>(());
}

#[test]
fn exit_without_shutdown() {
    let con = Connection::initialized(&["/foo/bar"]);
    con.notify::<lsp_types::notification::Exit>(());
}

#[test]
fn diagnostics_for_saved_files() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]

        [file pkg/__init__.py]
        from pkg.foo import Foo
        from pkg.foo import Bar

        1()

        [file pkg/foo.py]
        class Foo: ...
        lala
        "#,
    )
    .into_server();

    // Diagnostics for __init__.py (Check JSON)
    server.request_and_expect_json::<DocumentDiagnosticRequest>(
        DocumentDiagnosticParams {
            text_document: server.doc_id("pkg/__init__.py"),
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
        json!({
            "items": [
                {
                  "code": "attr-defined",
                  "message": "Module \"pkg.foo\" has no attribute \"Bar\"",
                  "range": {
                    "start": {
                      "line": 2,
                      "character": 21,
                    },
                    "end": {
                      "line": 2,
                      "character": 24,
                    },
                  },
                  "severity": 1,
                  "source": "zubanls"
                },
                {
                  "code": "operator",
                  "message": "\"int\" not callable",
                  "range": {
                    "start": {
                      "line": 4,
                      "character": 1,
                    },
                    "end": {
                      "line": 4,
                      "character": 4,
                    },
                  },
                  "severity": 1,
                  "source": "zubanls"
                },
            ],
            "kind": "full"
        }),
    );

    // Diagnostics for foo.py (Check full serialization)
    {
        let res = server.request::<DocumentDiagnosticRequest>(DocumentDiagnosticParams {
            text_document: server.doc_id("pkg/foo.py"),
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
        let DocumentDiagnosticReportResult::Report(DocumentDiagnosticReport::Full(report)) = res
        else {
            unreachable!()
        };
        // For now
        assert!(report.related_documents.is_none());
        let items = report.full_document_diagnostic_report.items;
        assert_eq!(items.len(), 1);
        let diagnostic = &items[0];
        assert_eq!(diagnostic.message, "Name \"lala\" is not defined");
        assert_eq!(
            diagnostic.code,
            Some(NumberOrString::String("name-defined".into()))
        );
    }

    // Diagnostics for a file that does not exist
    {
        let response =
            server.request_with_response::<DocumentDiagnosticRequest>(DocumentDiagnosticParams {
                text_document: server.doc_id("pkg/undefined.py"),
                identifier: None,
                previous_result_id: None,
                partial_result_params: PartialResultParams::default(),
                work_done_progress_params: WorkDoneProgressParams::default(),
            });
        let error = response.error.unwrap();
        assert!(error.message.contains("does not exist"));
        assert_eq!(error.code, lsp_server::ErrorCode::InvalidParams as i32);
    }
}

#[test]
fn in_memory_file_changes() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]

        [file pkg/__init__.py]
        from pkg.foo import x
        reveal_type(x)

        [file pkg/foo.py]
        x = 3
        "#,
    )
    .into_server();

    const FOO_PATH: &str = "pkg/foo.py";

    let expect_request = |id, expected_init: Vec<String>, expected_foo: Vec<String>| {
        let actual_foo = server.diagnostics_for_file(FOO_PATH);
        let actual_init = server.diagnostics_for_file("pkg/__init__.py");
        assert_eq!(actual_foo, expected_foo, "in request {id:?} (foo.py)");
        assert_eq!(actual_init, expected_init, "in request {id} (__init__.py)");
    };

    let revealed_type_int = "Revealed type is \"builtins.int\"".to_string();
    let revealed_type_str = "Revealed type is \"builtins.str\"".to_string();
    let revealed_type_bytes = "Revealed type is \"builtins.bytes\"".to_string();
    let revealed_type_any = "Revealed type is \"Any\"".to_string();
    expect_request("initially", vec![revealed_type_int.clone()], vec![]);

    server.notify::<DidOpenTextDocument>(DidOpenTextDocumentParams {
        text_document: TextDocumentItem {
            uri: server.doc_id(FOO_PATH).uri,
            language_id: "python".to_owned(),
            version: 0,
            text: "x = ''\n".to_owned(),
        },
    });

    expect_request("after opening", vec![revealed_type_str.clone()], vec![]);
    server.write_file_and_wait(FOO_PATH, "x = 1()\n");
    expect_request("after FS write", vec![revealed_type_str], vec![]);

    let change_foo_to = |text, version| {
        server.notify::<DidChangeTextDocument>(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: server.doc_id(FOO_PATH).uri,
                version,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                text,
                range: None,
                range_length: None,
            }],
        });
    };

    change_foo_to("x=b''\n".to_string(), 1);

    expect_request("after first DidChange", vec![revealed_type_bytes], vec![]);

    change_foo_to("x=1\n1.0()\n".to_string(), 2);

    expect_request(
        "after second DidChange",
        vec![revealed_type_int],
        vec!["\"float\" not callable".to_string()],
    );

    server.notify::<DidCloseTextDocument>(DidCloseTextDocumentParams {
        text_document: server.doc_id(FOO_PATH),
    });
    expect_request(
        "after close",
        vec![revealed_type_any],
        vec!["\"int\" not callable".to_string()],
    );
    // Delete the file and check that it returns the correct error when requesting diagnostics
    server.remove_file_and_wait(FOO_PATH);

    let response =
        server.request_with_response::<DocumentDiagnosticRequest>(DocumentDiagnosticParams {
            text_document: server.doc_id(FOO_PATH),
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let error = response.error.expect("Expected an error");
    assert!(response.result.is_none());
    assert!(error.message.contains("does not exist"));
    assert_eq!(error.code, lsp_server::ErrorCode::InvalidParams as i32);
}

#[test]
fn change_config_file() {
    let server = Project::with_fixture(
        r#"
        [file mypy.ini]

        [file foo.py]
        def foo(x: int): ...
        "#,
    )
    .into_server();

    let expect_diagnostics = |id, expected: Vec<String>| {
        assert_eq!(
            server.diagnostics_for_file("foo.py"),
            expected,
            "in request {id:?} (foo.py)"
        );
    };

    expect_diagnostics("initially", vec![]);

    server.write_file_and_wait("mypy.ini", "[mypy]\nstrict = True");

    const MISSING: &str = "Function is missing a return type annotation";
    expect_diagnostics("After modifying", vec![MISSING.to_string()]);

    server.remove_file_and_wait("mypy.ini");

    expect_diagnostics("After deleting", vec![]);

    server.write_file_and_wait(".mypy.ini", "[mypy]\nstrict = True\n");

    expect_diagnostics("After creating a new .mypy.ini", vec![MISSING.to_string()]);

    server.write_file_and_wait("mypy.ini", "");

    expect_diagnostics("After overwriting .mypy.ini with mypy.ini", vec![]);
}

#[test]
fn check_rename_without_symlinks() {
    check_rename(false);
}

#[test]
#[cfg(not(windows))] // windows requires elevated permissions to create symlinks
fn check_rename_with_symlinks() {
    check_rename(true);
}

fn check_rename(contains_symlink: bool) {
    let mut project = Project::with_fixture(
        r#"
        [file check.py]
        import foo
        import bar
        import pkg.foo

        [file foo.py]
        def foo(x: int): ...
        "#,
    );
    if contains_symlink {
        project = project.with_root_dir_contains_symlink()
    }
    let server = project.into_server();

    const NO_FOO: &str = "Cannot find implementation or library stub for module named \"foo\"";
    const NO_BAR: &str = "Cannot find implementation or library stub for module named \"bar\"";
    const NO_PKG: &str = "Cannot find implementation or library stub for module named \"pkg\"";
    const NO_PKG_FOO: &str =
        "Cannot find implementation or library stub for module named \"pkg.foo\"";

    let d = || server.diagnostics_for_file("check.py");

    assert_eq!(d(), vec![NO_BAR.to_string(), NO_PKG.to_string()]);

    server.rename_file_and_wait("foo.py", "bar.py");

    assert_eq!(d(), vec![NO_FOO.to_string(), NO_PKG.to_string()]);

    server.create_dir_all_and_wait("pkg");

    assert_eq!(d(), vec![NO_FOO.to_string(), NO_PKG_FOO.to_string()]);

    server.rename_file_and_wait("bar.py", "pkg/foo.py");

    assert_eq!(d(), vec![NO_FOO.to_string(), NO_BAR.to_string()]);

    server.write_file_and_wait("foo.py", "");
    server.write_file_and_wait("bar.py", "");

    assert_eq!(d(), Vec::<String>::default());

    server.tmp_dir.remove_file("foo.py");
    server.tmp_dir.remove_file("bar.py");
    server.remove_file_and_wait("pkg/foo.py");

    assert_eq!(
        d(),
        vec![
            NO_FOO.to_string(),
            NO_BAR.to_string(),
            NO_PKG_FOO.to_string()
        ]
    );
}

#[test]
fn multi_roots() {
    let server = Project::with_fixture(
        r#"
        [file mypy.ini]

        [file p1/check.py]
        import foo
        import bar
        import undefined

        [file p1/foo.py]

        [file p2/bar.py]
        "#,
    )
    .root("p1")
    .root("p2")
    .into_server();

    let d = || server.diagnostics_for_file("p1/check.py");
    const UNDEF: &str = "Cannot find implementation or library stub for module named \"undefined\"";
    const NO_BAR: &str = "Cannot find implementation or library stub for module named \"bar\"";

    assert_eq!(d(), vec![UNDEF.to_string()]);

    server.tmp_dir.remove_file("p2/bar.py");
    server.rename_file_and_wait("p1/foo.py", "p2/foo.py");

    assert_eq!(d(), vec![NO_BAR.to_string(), UNDEF.to_string()]);
    server.write_file_and_wait("p2/bar.py", "1()");

    assert_eq!(d(), vec![UNDEF.to_string()]);
}
