//! The most high-level integrated tests for Zuban (copied from rust-analyzer).
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
    CompletionItemKind, CompletionParams, DiagnosticServerCapabilities, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, DocumentHighlightKind,
    DocumentHighlightParams, DocumentSymbolParams, GotoDefinitionParams, HoverParams,
    NumberOrString, PartialResultParams, Position, PositionEncodingKind, Range, ReferenceContext,
    ReferenceParams, RenameParams, SelectionRangeParams, SemanticToken, SemanticTokenType,
    SemanticTokens, SemanticTokensParams, SemanticTokensRangeParams,
    SemanticTokensServerCapabilities, SignatureHelpParams, SymbolKind,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentPositionParams, Uri,
    WorkDoneProgressParams, WorkspaceSymbolParams,
    request::{
        Completion, DocumentDiagnosticRequest, DocumentHighlightRequest, DocumentSymbolRequest,
        GotoDeclaration, GotoDefinition, GotoImplementation, GotoTypeDefinition, HoverRequest,
        PrepareRenameRequest, References, Rename, SelectionRangeRequest, SemanticTokensFullRequest,
        SemanticTokensRangeRequest, SignatureHelpRequest, WorkspaceSymbolRequest,
    },
};

mod connection;
mod support;

use connection::Connection;
use serde::Deserialize as _;
use serde_json::{Value, json};
// It is very unfortunate, but we need to tag every test in this crate, to avoid having set_hook
// overwritten by the thread spawning? test setup? I'm not sure what it is exactly, but I have seen
// cases where the panic hook disappeared from tests and would be reverted to the default one,
// which is obviously very unfortunate.
// https://users.rust-lang.org/t/is-there-any-way-to-set-panic-hook-reliably-in-the-test/18202
use serial_test::{parallel, serial};
use support::Project;

#[test]
#[parallel]
fn basic_server_setup() {
    let con = Connection::new();
    let response = con.initialize(&["/foo/bar"], None, true);

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
#[parallel]
fn request_after_shutdown_is_invalid() {
    let con = Connection::initialized(&["/foo/bar"], None, true);
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
#[parallel]
fn exit_without_shutdown() {
    let con = Connection::initialized(&["/foo/bar"], None, true);
    con.notify::<lsp_types::notification::Exit>(());
}

#[test]
#[serial]
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
                      "line": 1,
                      "character": 20,
                    },
                    "end": {
                      "line": 1,
                      "character": 23,
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
                      "line": 3,
                      "character": 0,
                    },
                    "end": {
                      "line": 3,
                      "character": 3,
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
#[parallel]
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

    server.open_in_memory_file(FOO_PATH, "x = ''\n");

    expect_request("after opening", vec![revealed_type_str.clone()], vec![]);
    server.write_file_and_wait(FOO_PATH, "x = 1()\n");
    expect_request("after FS write", vec![revealed_type_str], vec![]);

    server.change_in_memory_file(FOO_PATH, "x=b''\n");

    expect_request("after first DidChange", vec![revealed_type_bytes], vec![]);

    server.change_in_memory_file(FOO_PATH, "x=1\n1.0()\n");

    expect_request(
        "after second DidChange",
        vec![revealed_type_int],
        vec!["\"float\" not callable".to_string()],
    );

    server.close_in_memory_file(FOO_PATH);
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
#[serial]
fn change_config_file() {
    let server = Project::with_fixture(
        r#"
        [file mypy.ini]

        [file foo.py]
        def foo(x: int): ...
        "#,
    )
    .into_server();

    // Open an in memory file that doesn't otherwise exist
    server.open_in_memory_file("in_mem.py", "def f(x: int): x()");

    let req = |name| server.diagnostics_for_file(name);
    let expect_diagnostics = |id, expected_foo: Vec<String>| {
        assert_eq!(req("foo.py"), expected_foo, "in request {id:?} (foo.py)");
    };

    const NOT_CALLABLE: &str = r#""int" not callable"#;
    assert_eq!(req("in_mem.py"), vec![NOT_CALLABLE]);
    expect_diagnostics("initially", vec![]);

    server.write_file_and_wait("mypy.ini", "[mypy]\nstrict = True");
    // This test kept failing in CI (probably because of stolen time, so add an additional long
    // sleep here.
    std::thread::sleep(std::time::Duration::from_millis(10));

    const MISSING: &str = "Function is missing a return type annotation";
    expect_diagnostics("After modifying", vec![MISSING.to_string()]);
    assert_eq!(req("in_mem.py"), vec![MISSING, NOT_CALLABLE]);

    server.remove_file_and_wait("mypy.ini");

    expect_diagnostics("After deleting", vec![]);
    assert_eq!(req("in_mem.py"), vec![NOT_CALLABLE]);

    server.write_file_and_wait(".mypy.ini", "[mypy]\nstrict = True\n");

    expect_diagnostics("After creating a new .mypy.ini", vec![MISSING.to_string()]);
    assert_eq!(req("in_mem.py"), vec![MISSING, NOT_CALLABLE]);

    server.write_file_and_wait("mypy.ini", "");

    expect_diagnostics("After overwriting .mypy.ini with mypy.ini", vec![]);
    assert_eq!(req("in_mem.py"), vec![NOT_CALLABLE]);
}

#[test]
#[serial]
fn check_rename_without_symlinks() {
    if !symlink_creation_allowed() {
        return;
    }
    check_rename(false);
}

#[test]
#[serial]
fn check_rename_with_symlinks() {
    if !symlink_creation_allowed() {
        return;
    }
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
#[parallel]
fn multi_roots() {
    let server = Project::with_fixture(
        r#"
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

#[test]
#[serial]
fn files_outside_of_root() {
    let server = Project::with_fixture(
        r#"
        [file base/m.py]
        import outside_workdir
        import outside_in_mem
        import foo

        [file base/foo.py]

        [file outside_workdir.py]
        import foo

        [file base/with space.py]
        b''()

        "#,
    )
    .root("base")
    .into_server();

    let d = |name| server.diagnostics_for_file(name);
    const NO_OUTSIDE1: &str =
        "Cannot find implementation or library stub for module named \"outside_workdir\"";
    const NO_OUTSIDE2: &str =
        "Cannot find implementation or library stub for module named \"outside_in_mem\"";

    server.open_in_memory_file("outside_in_mem.py", "import foo");
    assert!(d("outside_in_mem.py").is_empty());
    // Since it's not an in-memory file, it's out of scope and diagnostics are not available
    let response =
        server.request_with_response::<DocumentDiagnosticRequest>(DocumentDiagnosticParams {
            text_document: TextDocumentIdentifier {
                uri: Uri::from_str(&format!(
                    "file://{}/outside_workdir.py",
                    server.tmp_dir.path_for_uri()
                ))
                .unwrap(),
            },
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
    let err = response.error.unwrap();
    assert!(err.message.ends_with("outside_workdir.py does not exist"));
    assert_eq!(err.code, lsp_server::ErrorCode::InvalidParams as i32);

    assert_eq!(
        d("base/m.py"),
        vec![NO_OUTSIDE1.to_string(), NO_OUTSIDE2.to_string()]
    );

    assert_eq!(d("base/with%20space.py"), [r#""bytes" not callable"#]);

    // Check random files that don't really make sense
    let check_other_uris = [
        Uri::from_str("file:///bar/foo").unwrap(),
        Uri::from_str("file://foo").unwrap(),
        Uri::from_str("file://").unwrap(),
        Uri::from_str("https://www.example.com/foo.py").unwrap(),
        Uri::from_str("file:/single_slash").unwrap(),
    ];

    let diags_for_uri = |uri: &Uri| {
        server
            .full_diagnostics_for_abs_path(TextDocumentIdentifier { uri: uri.clone() })
            .into_iter()
            .map(|d| d.message)
            .collect::<Vec<_>>()
    };

    for uri in &check_other_uris {
        server.open_in_memory_file_for_uri(uri.clone(), "import m\n1()");
        assert_eq!(diags_for_uri(uri), vec![r#""int" not callable"#]);
    }

    server.open_in_memory_file("base/m.py", "import outside_workdir\nimport foo");
    assert_eq!(d("base/m.py"), vec![NO_OUTSIDE1.to_string()]);

    // The in memory files should still work after a panic
    server.raise_and_recover_panic_in_language_server();

    assert!(d("outside_in_mem.py").is_empty());
    assert_eq!(d("base/m.py"), vec![NO_OUTSIDE1.to_string()]);

    for uri in &check_other_uris {
        assert_eq!(diags_for_uri(uri), vec![r#""int" not callable"#]);
    }
}

#[test]
#[serial]
fn files_outside_of_root_with_push_diagnostics() {
    let server = Project::with_fixture(
        r#"
        [file base/m.py]
        import outside_workdir
        import outside_in_mem
        import foo

        [file base/foo.py]

        [file outside_workdir.py]
        import foo

        "#,
    )
    .root("base")
    .with_push_diagnostics()
    .into_server();

    const NO_OUTSIDE: &str =
        "Cannot find implementation or library stub for module named \"outside_workdir\"";

    server.open_in_memory_file("outside_in_mem.py", "import foo");
    assert!(
        server
            .expect_publish_diagnostics_for_file("outside_in_mem.py")
            .is_empty()
    );

    server.open_in_memory_file("base/m.py", "import outside_workdir\nimport foo");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("base/m.py"),
        [NO_OUTSIDE]
    );

    // Check random files that don't really make sense
    let mut check_other_uris = vec![
        Uri::from_str("file:///bar/foo").unwrap(),
        Uri::from_str("file://foo").unwrap(),
        Uri::from_str("file://").unwrap(),
        Uri::from_str("https://www.example.com/foo.py").unwrap(),
        Uri::from_str("file:/single_slash").unwrap(),
    ];

    if cfg!(windows) {
        check_other_uris.pop();
        check_other_uris.push(Uri::from_str("file:/C:/single_slash").unwrap());
    }

    for uri in &mut check_other_uris {
        server.open_in_memory_file_for_uri(uri.clone(), "import m\n1()");
        let (file, diags) = server.expect_publish_diagnostics_with_uri();
        if uri.authority().is_none() {
            // Make sure all uris have an authority, because that's how zubanls returns it.
            *uri = Uri::from_str(&uri.as_str().replace("file:/", "file:///")).unwrap();
        }
        if cfg!(windows) && (uri.as_str() == "file://foo" || uri.as_str() == "file://") {
            // TODO this is probably a bug in Windows handling, but for now this shouldn't matter
            // and we leave it like that as long as it does not crash. Also these paths don't
            // really exist on Windows
            *uri = Uri::from_str(&uri.as_str().replace("file:/", "file://")).unwrap();
        }
        assert_eq!(file.as_str(), uri.as_str());
        assert_eq!(diags, [r#""int" not callable"#]);
    }

    let in_mem_uri = &format!("file://{}/outside_in_mem.py", server.tmp_dir.path_for_uri());
    let m_uri = &format!("file://{}/base/m.py", server.tmp_dir.path_for_uri());
    // The in memory files should still work after a panic
    server.raise_and_recover_panic_in_language_server();
    let mut expected: Vec<_> = check_other_uris
        .iter()
        .map(|uri| (uri.as_str(), vec![r#""int" not callable"#]))
        .collect();
    expected.push((in_mem_uri, vec![]));
    expected.push((m_uri, vec![NO_OUTSIDE]));
    let expected: std::collections::HashMap<_, _> = expected.into_iter().collect();
    server.expect_multiple_diagnostics_pushes_with_uris(expected);
}

#[test]
#[parallel]
fn symlinks_with_dir_loop() {
    if !symlink_creation_allowed() {
        return;
    }
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        from nested import foo
        from nested.nested import foo as bar
        from typing import Any, assert_type
        import simple_symlink
        import simple_symlink_dir
        import simple_symlink_dir2

        assert_type(foo.x, Any)
        assert_type(simple_symlink.x, str)
        assert_type(simple_symlink_dir.x, bytes)
        assert_type(simple_symlink_dir2.x, float)

        x = 3

        [file simple_file.py]
        x = ""
        [file simple_symlink_dir/file.py]
        x = b''
        [file simple_symlink_dir2/__init__.py.indirect]
        x = 1.0
        "#,
    )
    .into_server();

    server.tmp_dir.create_symlink_file(
        "simple_symlink_dir/file.py",
        "simple_symlink_dir/__init__.py",
    );
    // It is important to test that links can also be relative paths and not just absolute paths.
    server
        .tmp_dir
        .create_relative_symlink_file("__init__.py.indirect", "simple_symlink_dir2/__init__.py");
    server
        .tmp_dir
        .create_symlink_file("simple_file.py", "simple_symlink.py");

    let cannot_find =
        |name| format!(r#"Cannot find implementation or library stub for module named "{name}""#);

    let d = || server.diagnostics_for_file("foo.py");

    assert_eq!(d(), vec![cannot_find("nested"), cannot_find("nested"),]);

    // Create a loop
    server.create_symlink_dir_and_wait(".", "nested");

    assert_eq!(d(), vec![cannot_find("nested"), cannot_find("nested"),]);
}

#[test]
#[parallel]
fn diagnostics_positions() {
    use PositionEncodingKind as P;
    for (start_column, len, client_encodings) in [
        (6, 2, None),
        (8, 4, Some(vec![P::UTF8])),
        (6, 2, Some(vec![P::UTF16])),
        (5, 1, Some(vec![P::UTF32])),
        (8, 4, Some(vec![P::UTF8, P::UTF16, P::UTF32])),
    ] {
        let server = Project::with_fixture(
            r#"
            [file m.py]
            '𐐀'; 𐐀
            "#,
        )
        .into_server_detailed(client_encodings.clone());
        let diagnostics = server.full_diagnostics_for_file("m.py");
        assert_eq!(diagnostics.len(), 1);
        let diagnostic = diagnostics.into_iter().next().unwrap();
        assert_eq!(diagnostic.message, "Name \"𐐀\" is not defined");
        assert_eq!(diagnostic.range.start.line, 0);
        assert_eq!(diagnostic.range.end.line, 0);
        assert_eq!(
            diagnostic.range.start.character, start_column,
            "{client_encodings:?}"
        );
        assert_eq!(
            diagnostic.range.end.character,
            start_column + len,
            "{client_encodings:?}"
        );
    }
}

#[test]
#[serial]
fn check_panic_recovery() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        b''()
        [file bar.py]
        ""()
        "#,
    )
    .into_server();

    // Open an in memory file that doesn't otherwise exist, also add a forward reference that might
    // create an additional file and potential issues with panic recovery.
    server.open_in_memory_file("in_mem.py", "1()\nx: 'int' = 0");

    let req = |name| server.diagnostics_for_file(name);

    // Check before panic (bar.py is intentionally not checked!)
    assert_eq!(req("foo.py"), vec![r#""bytes" not callable"#]);
    assert_eq!(req("in_mem.py"), vec![r#""int" not callable"#]);

    // Introduce a panic
    server.raise_and_recover_panic_in_language_server();

    // Check that the files (especially in memory files) are still working
    assert_eq!(req("foo.py"), vec![r#""bytes" not callable"#]);
    assert_eq!(req("bar.py"), vec![r#""str" not callable"#]);
    assert_eq!(req("in_mem.py"), vec![r#""int" not callable"#]);

    // Check that in memory files can be changed after a panic
    server.change_in_memory_file("in_mem.py", "");
    assert!(server.diagnostics_for_file("in_mem.py").is_empty());
}

#[test]
#[serial]
fn check_panic_recovery_with_push_diagnostics() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        b''()
        "#,
    )
    .with_push_diagnostics()
    .into_server();

    const NOT_CALLABLE: &str = r#""int" not callable"#;
    // Open an in memory file that doesn't otherwise exist
    server.open_in_memory_file("in_mem.py", "1()");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("in_mem.py"),
        [NOT_CALLABLE]
    );

    // Introduce a panic
    server.raise_and_recover_panic_in_language_server();
    assert_eq!(
        server.expect_publish_diagnostics_for_file("in_mem.py"),
        [NOT_CALLABLE]
    );

    // Check that in memory files can be changed after a panic
    server.change_in_memory_file("in_mem.py", "");
    assert!(
        server
            .expect_publish_diagnostics_for_file("in_mem.py")
            .is_empty()
    );
}

#[cfg(target_os = "windows")]
fn symlink_creation_allowed() -> bool {
    static SYMLINK_CREATION: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SYMLINK_CREATION.get_or_init(|| {
        let temp_dir = std::env::temp_dir();
        let link = temp_dir.join("zuban-test-symlink-creation");
        let result = std::os::windows::fs::symlink_dir(temp_dir, &link).is_ok();
        if let Err(err) = std::fs::remove_dir(link) {
            eprintln!("Symlink deletion did not work: {err}")
        }
        result
    })
}

#[cfg(not(target_os = "windows"))]
fn symlink_creation_allowed() -> bool {
    true
}

#[test]
#[serial]
fn publish_diagnostics_without_symlinks() {
    if fails_too_much_on_linux_and_github_actions() {
        return;
    }
    publish_diagnostics(false)
}

#[test]
#[serial]
fn publish_diagnostics_with_symlinks() {
    if fails_too_much_on_linux_and_github_actions() {
        return;
    }
    if !symlink_creation_allowed() {
        return;
    }
    publish_diagnostics(true)
}

fn publish_diagnostics(with_symlinks: bool) {
    // Check PublishDiagnostics where the client is not requesting diagnostics, but receiving them
    // each time a change is made
    let mut project = Project::with_fixture(
        r#"
            [file exists_in_fs.py]
            [file unrelated.py]
            "#,
    )
    .with_push_diagnostics();
    if with_symlinks {
        project = project.with_root_dir_contains_symlink()
    }
    let server = project.into_server();

    const NOT_CALLABLE: &str = r#""int" not callable"#;
    const NOT_CALLABLE2: &str = r#""str" not callable"#;
    const MODULE_MISSING: &str =
        r#"Cannot find implementation or library stub for module named "m""#;
    const ATTR_MISSING: &str = r#"Module "m" has no attribute "C""#;

    server.open_in_memory_file("exists_in_fs.py", "import m");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("exists_in_fs.py"),
        [MODULE_MISSING]
    );

    server.open_in_memory_file("not_exists_in_fs.py", "import m");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("not_exists_in_fs.py"),
        [MODULE_MISSING]
    );

    // Writing this file does not do anything, because it exists as an in memory file
    server.write_file_and_wait("not_exists_in_fs.py", "");

    server.change_in_memory_file("exists_in_fs.py", "from m import C\n1()\n");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("exists_in_fs.py"),
        [MODULE_MISSING, NOT_CALLABLE]
    );

    server.change_in_memory_file("not_exists_in_fs.py", "from m import C\n''()\n");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("not_exists_in_fs.py"),
        [MODULE_MISSING, NOT_CALLABLE2]
    );

    server.write_file_and_wait("m.py", "class C: ...");
    server.expect_multiple_diagnostics_pushes([
        ("exists_in_fs.py", vec![NOT_CALLABLE]),
        ("not_exists_in_fs.py", vec![NOT_CALLABLE2]),
    ]);

    // Should not generate a diagnostic
    server.write_file_and_wait("exists_in_fs.py", "['']()");

    server.open_in_memory_file("m.py", "");
    server.expect_multiple_diagnostics_pushes([
        ("m.py", vec![]),
        ("exists_in_fs.py", vec![ATTR_MISSING, NOT_CALLABLE]),
        ("not_exists_in_fs.py", vec![ATTR_MISSING, NOT_CALLABLE2]),
    ]);

    server.close_in_memory_file("m.py");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("not_exists_in_fs.py"),
        [NOT_CALLABLE2]
    );
    assert_eq!(
        server.expect_publish_diagnostics_for_file("exists_in_fs.py"),
        [NOT_CALLABLE]
    );

    // Should not generate a diagnostic
    server.write_file_and_wait("not_exists_in_fs.py", "[1]()");

    server.close_in_memory_file("not_exists_in_fs.py");
    if cfg!(target_os = "windows") {
        // Try to make sure the events are properly ordered
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    server.write_file_and_wait("m.py", "");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("exists_in_fs.py"),
        [ATTR_MISSING, NOT_CALLABLE]
    );
    server.remove_file_and_wait("m.py");
    assert_eq!(
        server.expect_publish_diagnostics_for_file("exists_in_fs.py"),
        [MODULE_MISSING, NOT_CALLABLE]
    );
    tracing::info!("Finished all checks");
}

fn fails_too_much_on_linux_and_github_actions() -> bool {
    cfg!(target_os = "linux") && std::env::var("GITHUB_ACTIONS").ok().as_deref() == Some("true")
}

#[test]
#[serial]
fn test_virtual_environment() {
    if fails_too_much_on_linux_and_github_actions() {
        // Somehow this test is failing a bit too often on GitHub, so for now ignore it.
        return;
    }

    let run = |expected_first: &[String], expected_second: Option<&[String]>| {
        let server = Project::with_fixture(if cfg!(windows) {
            r#"
                [file venv/Scripts/python.exe]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/Lib/site-packages/foo/__init__.py]
                foo = 1

                [file venv/Lib/site-packages/foo/py.typed]

                [file venv/Lib/site-packages/bar.py]
                bar = ''
                1()
                "#
        } else {
            r#"
                [file venv/bin/python]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/lib/python3.12/site-packages/foo/__init__.py]
                foo = 1

                [file venv/lib/python3.12/site-packages/foo/py.typed]

                [file venv/lib/python3.12/site-packages/bar.py]
                bar = ''
                1()
                "#
        })
        .with_push_diagnostics()
        .into_server();

        const PATH: &str = "check.py";

        let _span = tracing::info_span!("test_virtual_environment").entered();

        server.open_in_memory_file(PATH, "from foo import foo\nfrom bar import bar");

        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            expected_first,
        );

        if let Some(expected_second) = expected_second {
            tracing::info!("Remove it by renaming it");
            let old_path = if cfg!(windows) {
                "venv/Lib/site-packages/foo"
            } else {
                "venv/lib/python3.12/site-packages/foo"
            };
            let new_path = if cfg!(windows) {
                "venv/Lib/site-packages/foo_new"
            } else {
                "venv/lib/python3.12/site-packages/foo_new"
            };
            server.rename_file_and_wait(old_path, new_path);
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                expected_second,
            );
            server.rename_file_and_wait(new_path, old_path);
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                expected_first,
            );

            tracing::info!("Check if rewriting the file causes an issue now");
            let init = &format!("{old_path}/__init__.py");
            server.write_file_and_wait(init, "\n");
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                ["Module \"foo\" has no attribute \"foo\"".to_string()],
            );

            tracing::info!("Check adding the code again");
            server.write_file_and_wait(init, "foo = 1");
            let mut result = server.expect_publish_diagnostics_for_file(PATH);
            if cfg!(target_os = "windows") && !result.is_empty() {
                // On Windows events may be duplicated, because there is a Create event for writing
                // and then a modification event.
                result = server.expect_publish_diagnostics_for_file(PATH);
            }
            assert!(result.is_empty(), "{result:?}");

            tracing::info!("Check removing it");
            server.remove_file_and_wait(init);
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                ["Module \"foo\" has no attribute \"foo\"".to_string()],
            );

            tracing::info!("Check adding it again");
            server.write_file_and_wait(init, "foo = 1");
            assert!(server.expect_publish_diagnostics_for_file(PATH).is_empty());
        } else {
            // There is no watch on the venv dir if the environment variable is not set. Therefore
            // we cannot wait for an event. So we simply remove it.
            server.tmp_dir.remove_file(if cfg!(windows) {
                "venv/Lib/site-packages/foo/__init__.py"
            } else {
                "venv/lib/python3.12/site-packages/foo/__init__.py"
            })
        }
    };

    let import_err = |name: &str| {
        format!("Cannot find implementation or library stub for module named \"{name}\"")
    };

    tracing::info!("set venv information via $VIRTUAL_ENV");
    unsafe { std::env::set_var("VIRTUAL_ENV", "venv") };
    run(&[], Some(&[import_err("foo")]));
    unsafe { std::env::remove_var("VIRTUAL_ENV") };

    tracing::info!(
        "test_virtual_environment - After unsetting it, there should still be no errors, because the venv is found"
    );
    run(&[], Some(&[import_err("foo")]));
}

#[test]
#[serial]
fn test_virtual_env_with_pth_into_working_dir() {
    // The goal here is to reproduce setting similar to uv workspaces

    if fails_too_much_on_linux_and_github_actions() {
        // Somehow this test is failing a bit too often on GitHub, so for now ignore it.
        return;
    }

    let (site_package_path, relative_path_to_other_project) = if cfg!(windows) {
        ("venv/Lib/site-packages", "../../../other_project")
    } else {
        (
            "venv/lib/python3.12/site-packages",
            "../../../../other_project",
        )
    };
    let server = Project::with_fixture(&format!(
        r#"
            [file venv/bin/python]

            [file venv/pyvenv.cfg]
            include-system-site-packages = false
            version = 3.12.3

            [file {site_package_path}/foo/__init__.py]
            foo = 1
            1()

            [file {site_package_path}/foo/py.typed]
            1()

            [file {site_package_path}/frompth.pth]
            {relative_path_to_other_project}

            [file other_project/other_project/__init__.py]
            1()
            x = 1
            [file other_project/other_project/py.typed]
            "#
    ))
    .into_server();

    const PATH: &str = "check.py";

    server.open_in_memory_file(PATH, "from other_project import x\nreveal_type(x)");

    assert_eq!(
        server.diagnostics_for_file(PATH),
        [r#"Revealed type is "builtins.int""#]
    );
    assert_eq!(
        server.diagnostics_for_file("other_project/other_project/__init__.py"),
        [r#""int" not callable"#]
    );
}

#[test]
#[serial]
fn remove_directory_of_in_memory_file_without_push() {
    let server = Project::with_fixture(
        r#"
        [file foo/exists.py]
        "#,
    )
    .into_server();

    let path = "foo/does_not_exist.py";
    server.open_in_memory_file(path, "from foo import exists");

    let d = || server.diagnostics_for_file(path);

    let current = d();
    assert!(current.is_empty(), "{current:?}");

    tracing::info!("Remove directory, while in-memory file should persist");
    server.remove_file_and_wait("foo/exists.py");
    server.remove_dir_and_wait("foo");

    assert_eq!(d(), ["Module \"foo\" has no attribute \"exists\""]);

    tracing::info!("Re-create directory, which should not mess with in-memory file");

    server.create_dir_all_and_wait("foo");
    assert_eq!(d(), ["Module \"foo\" has no attribute \"exists\""]);

    tracing::info!("Re-create dependency, which should fix import errors");
    server.write_file_and_wait("foo/exists.py", "");
    let current = d();
    assert!(current.is_empty(), "{current:?}");
}

#[test]
#[serial]
fn remove_directory_of_in_memory_file_with_push() {
    if fails_too_much_on_linux_and_github_actions() {
        return;
    }
    let server = Project::with_fixture(
        r#"
        [file foo/exists.py]
        "#,
    )
    .with_push_diagnostics()
    .into_server();

    let path = "foo/does_not_exist.py";
    server.open_in_memory_file(path, "from foo import exists");

    assert!(server.expect_publish_diagnostics_for_file(path).is_empty());

    tracing::info!("Remove directory, while in-memory file should persist");
    server.remove_file_and_wait("foo/exists.py");
    server.remove_dir_and_wait("foo");
    assert_eq!(
        server.expect_publish_diagnostics_for_file(path),
        ["Module \"foo\" has no attribute \"exists\""]
    );

    tracing::info!("Re-create directory, which should not mess with in-memory file");
    server.create_dir_all_and_wait("foo");
    if !cfg!(target_os = "windows") {
        assert_eq!(
            server.expect_publish_diagnostics_for_file(path),
            ["Module \"foo\" has no attribute \"exists\""]
        );
    }

    tracing::info!("Re-create dependency, which should fix import errors");
    server.write_file_and_wait("foo/exists.py", "");
    assert!(server.expect_publish_diagnostics_for_file(path).is_empty());

    tracing::info!("Change the in-memory file");
    server.change_in_memory_file(path, "from foo import exists\n1()");
    assert_eq!(
        server.expect_publish_diagnostics_for_file(path),
        ["\"int\" not callable"]
    );
}

#[test]
#[serial]
fn test_pyproject_with_mypy_config_dir_env_var() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]
        [project]
        name = "hello_zuban"
        version = "0.1.0"

        requires-python = ">= 3.12"
        dependencies = []

        [project.scripts]
        hello-zuban = "hello_zuban:entry_point"

        [tool.mypy]
        mypy_path = "$MYPY_CONFIG_FILE_DIR/src"
        files = ["$MYPY_CONFIG_FILE_DIR/src"]
        strict = true

        [file src/hello_zuban/__init__.py]
        from hello_zuban.hello import X
        from src.hello_zuban.hello import Z

        x = X()

        [file src/hello_zuban/hello.py]
        Z = 1
        class X: pass
        1()

        [file test/test_foo.py]
        ""()

        "#,
    )
    .into_server();

    assert_eq!(
        server.diagnostics_for_file("src/hello_zuban/__init__.py"),
        ["Cannot find implementation or library stub for module named \"hello_zuban\""]
    );
    assert_eq!(
        server.diagnostics_for_file("src/hello_zuban/hello.py"),
        ["\"int\" not callable"]
    );
    // It should work at least after opening, even if it's not on path.
    server.open_in_memory_file("test/test_foo.py", "''()");
    assert_eq!(
        server.diagnostics_for_file("test/test_foo.py"),
        ["\"str\" not callable"]
    );
}

#[test]
#[serial]
fn check_goto_likes() {
    let server = Project::with_fixture(
        r#"
        [file m.py]
        class Class:
            """
            doc 🫶 love 
            """

        d = Class()

        [file m.pyi]
        class Class: ...

        d: Class
        "#,
    )
    .into_server();

    // Open an in memory file that doesn't otherwise exist
    let path = "n.py";
    server.open_in_memory_file(
        path,
        "from m import d\nd\ninvalid_reference_for_rename\nimport pathlib",
    );

    let mpy = server.doc_id("m.py").uri;
    let mpyi = server.doc_id("m.pyi").uri;
    let npy = server.doc_id("n.py").uri;
    let pos = TextDocumentPositionParams::new(server.doc_id("n.py"), Position::new(1, 0));

    // Hover
    server.request_and_expect_json::<HoverRequest>(
        HoverParams {
            text_document_position_params: pos.clone(),
            work_done_progress_params: Default::default(),
        },
        json!({
            "contents": {
                "kind": "markdown",
                "value": "(variable) d: Class\n---\ndoc 🫶 love",
            },
            "range": {
                "start": {"line": 1, "character": 0},
                "end": {"line": 1, "character": 1},
            }
        }),
    );

    let params = GotoDefinitionParams {
        text_document_position_params: pos.clone(),
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };
    // Goto Declaration
    server.request_and_expect_json::<GotoDeclaration>(
        params.clone(),
        json!([{
            "targetUri": &npy,
            "targetSelectionRange": {
                "start": {"line": 0, "character": 14},
                "end": {"line": 0, "character": 15},
            },
            "targetRange": {
                "start": {"line": 0, "character": 0},
                "end": {"line": 0, "character": 15},
            },
        }]),
    );

    // Goto Definition
    server.request_and_expect_json::<GotoDefinition>(
        params.clone(),
        json!([{
            "targetUri": &mpy,
            "targetSelectionRange": {
                "start": {"line": 5, "character": 0},
                "end": {"line": 5, "character": 1},
            },
            "targetRange": {
                "start": {"line": 5, "character": 0},
                "end": {"line": 5, "character": 11},
            },
        }]),
    );
    // Goto Type Definition
    server.request_and_expect_json::<GotoTypeDefinition>(
        params.clone(),
        json!([{
            "targetUri": &mpyi,
            "targetSelectionRange": {
                "start": {"line": 2, "character": 0},
                "end": {"line": 2, "character": 1},
            },
            "targetRange": {
                "start": {"line": 2, "character": 0},
                "end": {"line": 2, "character": 8},
            },
        }]),
    );

    // Goto Definition on a target in Windows that should not lead to a path with a question mark start, see #118
    if cfg!(windows) {
        let result = server
            .connection
            .request_with_expected_response::<GotoDefinition>(GotoDefinitionParams {
                text_document_position_params: TextDocumentPositionParams::new(
                    server.doc_id("n.py"),
                    Position::new(3, 10),
                ),
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            });
        let Value::String(uri) = &result[0]["targetUri"] else {
            panic!("Expected an entry with an URI: {result:?}");
        };
        assert!(!uri.starts_with("file://///?"));
    }

    // Goto Implementation
    server.request_and_expect_json::<GotoImplementation>(
        params.clone(),
        json!([{
            "targetUri": &mpy,
            "targetSelectionRange": {
                "start": {"line": 0, "character": 6},
                "end": {"line": 0, "character": 11},
            },
            "targetRange": {
                "start": {"line": 0, "character": 0},
                "end": {"line": 5, "character": 0},
            },
        }]),
    );

    // References with add_declaration = true
    server.request_and_expect_json::<References>(
        ReferenceParams {
            text_document_position: pos.clone(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: ReferenceContext {
                include_declaration: true,
            },
        },
        json!([
          {
            "range": {
              "start": {
                "line": 5,
                "character": 0,
              },
              "end": {
                "line": 5,
                "character": 1,
              },
            },
            "uri": &mpy,
          },
          {
            "range": {
              "start": {
                "line": 2,
                "character": 0,
              },
              "end": {
                "line": 2,
                "character": 1,
              },
            },
            "uri": &mpyi,
          },
          {
            "range": {
              "start": {
                "line": 0,
                "character": 14,
              },
              "end": {
                "line": 0,
                "character": 15,
              },
            },
            "uri": &npy,
          },
          {
            "range": {
              "start": {
                "line": 1,
                "character": 0,
              },
              "end": {
                "line": 1,
                "character": 1,
              },
            },
            "uri": &npy,
          }
        ]),
    );
    // References with add_declaration = false
    server.request_and_expect_json::<References>(
        ReferenceParams {
            text_document_position: pos.clone(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: ReferenceContext {
                include_declaration: false,
            },
        },
        json!([
          {
            "range": {
              "start": {
                "line": 0,
                "character": 14,
              },
              "end": {
                "line": 0,
                "character": 15,
              },
            },
            "uri": &npy,
          },
          {
            "range": {
              "start": {
                "line": 1,
                "character": 0,
              },
              "end": {
                "line": 1,
                "character": 1,
              },
            },
            "uri": &npy,
          }
        ]),
    );

    // Document Highlights
    server.request_and_expect_json::<DocumentHighlightRequest>(
        DocumentHighlightParams {
            text_document_position_params: pos.clone(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!([
          {
            "range": {
              "start": {
                "line": 0,
                "character": 14,
              },
              "end": {
                "line": 0,
                "character": 15,
              },
            },
            "kind": DocumentHighlightKind::WRITE,
          },
          {
            "range": {
              "start": {
                "line": 1,
                "character": 0,
              },
              "end": {
                "line": 1,
                "character": 1,
              },
            },
            "kind": DocumentHighlightKind::READ,
          }
        ]),
    );

    // Prepare rename
    {
        server.request_and_expect_json::<PrepareRenameRequest>(
            TextDocumentPositionParams::new(server.doc_id("n.py"), Position::new(0, 0)),
            json!(None::<()>),
        );
        server.request_and_expect_json::<PrepareRenameRequest>(
            pos.clone(),
            json!({
              "start": {
                "line": 1,
                "character": 0,
              },
              "end": {
                "line": 1,
                "character": 1,
              },
            }),
        );
        let err = server
            .request_with_expected_error::<PrepareRenameRequest>(TextDocumentPositionParams::new(
                server.doc_id("n.py"),
                Position::new(2, 0),
            ))
            .message;
        assert_eq!(
            err,
            "The reference \"invalid_reference_for_rename\" cannot \
            be resolved; rename is therefore not possible."
        );
    }

    // Rename
    {
        // On "from" of the import
        let err = server.request_with_expected_error::<Rename>(RenameParams {
            text_document_position: TextDocumentPositionParams::new(
                server.doc_id("n.py"),
                Position::new(0, 0),
            ),
            // No change!
            new_name: "d".into(),
            work_done_progress_params: Default::default(),
        });
        assert_eq!(
            err.message,
            "Could not find a name under the cursor to rename"
        );

        // On "d"
        server.request_and_expect_json::<Rename>(
            RenameParams {
                text_document_position: pos.clone(),
                new_name: "new".into(),
                work_done_progress_params: Default::default(),
            },
            json!({
              "documentChanges": [
                {
                  "edits": [
                    {
                      "newText": "new",
                      "range": {
                        "start": {
                          "line": 2,
                          "character": 0,
                        },
                        "end": {
                          "line": 2,
                          "character": 1,
                        },
                      }
                    }
                  ],
                  "textDocument": {
                    "uri": &mpyi,
                    "version": null
                  }
                },
                {
                  "edits": [
                    {
                      "newText": "new",
                      "range": {
                        "start": {
                          "line": 5,
                          "character": 0,
                        },
                        "end": {
                          "line": 5,
                          "character": 1,
                        },
                      }
                    }
                  ],
                  "textDocument": {
                    "uri": &mpy,
                    "version": null
                  }
                },
                {
                  "edits": [
                    {
                      "newText": "new",
                      "range": {
                        "start": {
                          "line": 0,
                          "character": 14,
                        },
                        "end": {
                          "line": 0,
                          "character": 15,
                        },
                      }
                    },
                    {
                      "newText": "new",
                      "range": {
                        "start": {
                          "line": 1,
                          "character": 0,
                        },
                        "end": {
                          "line": 1,
                          "character": 1,
                        },
                      }
                    }
                  ],
                  "textDocument": {
                    "uri": &npy,
                    "version": null
                  }
                }
              ]
            }),
        );

        // On "d", but rename to "d" again
        server.request_and_expect_json::<Rename>(
            RenameParams {
                text_document_position: pos.clone(),
                // No change!
                new_name: "d".into(),
                work_done_progress_params: Default::default(),
            },
            json!(None::<()>),
        );

        // On "invalid_reference_for_rename", where we don't know its definition
        let err = server.request_with_expected_error::<Rename>(RenameParams {
            text_document_position: TextDocumentPositionParams::new(
                server.doc_id("n.py"),
                Position::new(2, 0),
            ),
            // No change!
            new_name: "d".into(),
            work_done_progress_params: Default::default(),
        });
        assert_eq!(
            err.message,
            "Could not find the definition of \"invalid_reference_for_rename\" under the cursor"
        );

        let dpy = server.doc_id("d.py").uri;
        let dpyi = server.doc_id("d.pyi").uri;
        // On the module "m" on import
        server.request_and_expect_json::<Rename>(
            RenameParams {
                text_document_position: TextDocumentPositionParams::new(
                    server.doc_id("n.py"),
                    Position::new(0, "from m".len() as u32),
                ),
                // No change!
                new_name: "d".into(),
                work_done_progress_params: Default::default(),
            },
            json!({
              "documentChanges": [
                {
                  "edits": [
                    {
                      "newText": "d",
                      "range": {
                        "start": {
                          "line": 0,
                          "character": 5,
                        },
                        "end": {
                          "character": 6,
                          "line": 0,
                        },
                      }
                    }
                  ],
                  "textDocument": {
                    "uri": &npy,
                    "version": null
                  }
                },
                {
                  "kind": "rename",
                  "oldUri": &mpy,
                  "newUri": &dpy,
                },
                {
                  "kind": "rename",
                  "oldUri": &mpyi,
                  "newUri": &dpyi,
                }
              ]
            }),
        );
    }
}

#[test]
#[serial]
fn check_completions() {
    let server = Project::with_fixture(
        r#"
        [file m.py]
        class MyClass:
            """
            doc 🫶 love 
            """

        def my_func(): ...
        "#,
    )
    .into_server();

    // Open an in memory file that doesn't otherwise exist
    let path = "n.py";
    server.open_in_memory_file(path, "import m\nm.my");

    let pos = TextDocumentPositionParams::new(server.doc_id("n.py"), Position::new(1, 4));
    server.request_and_expect_json::<Completion>(
        CompletionParams {
            text_document_position: pos,
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            context: None,
        },
        json!([
          {
            "kind": CompletionItemKind::CLASS,
            "label": "MyClass",
            "sortText": "00000",
            "textEdit": {
              "newText": "MyClass",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FUNCTION,
            "label": "my_func",
            "sortText": "00001",
            "textEdit": {
              "newText": "my_func",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__annotations__",
            "sortText": "00002",
            "textEdit": {
              "newText": "__annotations__",
              "range": {
                "end": {
                  "character": 4,
                  "line": 1
                },
                "start": {
                  "character": 2,
                  "line": 1
                }
              }
            }
          },
          {
            "kind": CompletionItemKind::PROPERTY,
            "label": "__dict__",
            "sortText": "00003",
            "textEdit": {
              "newText": "__dict__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__doc__",
            "sortText": "00004",
            "textEdit": {
              "newText": "__doc__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__file__",
            "sortText": "00005",
            "textEdit": {
              "newText": "__file__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__loader__",
            "sortText": "00006",
            "textEdit": {
              "newText": "__loader__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__name__",
            "sortText": "00007",
            "textEdit": {
              "newText": "__name__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__package__",
            "sortText": "00008",
            "textEdit": {
              "newText": "__package__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__spec__",
            "sortText": "00009",
            "textEdit": {
              "newText": "__spec__",
              "range": {
                "start": {
                  "line": 1,
                  "character": 2,
                },
                "end": {
                  "line": 1,
                  "character": 4,
                },
              }
            },
          }
        ]),
    );
}

#[test]
#[serial]
fn check_call_signatures() {
    let server = Project::with_fixture(r#""#).into_server();

    // Open an in memory file that doesn't otherwise exist
    let path = "n.py";

    let run = |code: String, column, json| {
        server.open_in_memory_file(path, &code);
        let pos = TextDocumentPositionParams::new(server.doc_id("n.py"), Position::new(1, column));
        server.request_and_expect_json::<SignatureHelpRequest>(
            SignatureHelpParams {
                text_document_position_params: pos,
                work_done_progress_params: Default::default(),
                context: None,
            },
            json,
        );
    };
    let base = "def f(x: int, y: str) -> bytes: ...";
    run(format!("{base}\nf()"), 0, json!(None::<()>));
    run(format!("{base}\nf()"), 1, json!(None::<()>));
    run(format!("{base}\nf()"), 3, json!(None::<()>));
    run(format!("{base}\nf(1)"), 4, json!(None::<()>));

    let empty_result = json!({
      "activeSignature": 0,
      "activeParameter": 0,
      "signatures": [
        {
          "activeParameter": 0,
          "label": "(x: int, y: str) -> bytes",
          "parameters": [
            {
              "label": "x"
            },
            {
              "label": "y"
            }
          ]
        }
      ]
    }
    );
    run(format!("{base}\nf()"), 2, empty_result.clone());
    run(format!("{base}\nf("), 2, empty_result);

    let with_y = json!({
      "activeSignature": 0,
      "activeParameter": 1,
      "signatures": [
        {
          "activeParameter": 1,
          "label": "(x: int, y: str) -> bytes",
          "parameters": [
            {
              "label": "x"
            },
            {
              "label": "y"
            }
          ]
        }
      ]
    });
    run(format!("{base}\nf(y=)"), 4, with_y.clone());
    run(format!("{base}\nf(y="), 4, with_y);

    run(
        format!("\nint(1)"),
        4,
        json!({
          "activeParameter": 0,
          "activeSignature": 0,
          "signatures": [
            {
              "activeParameter": 0,
              "label": "(x: str | Buffer | SupportsInt | SupportsIndex | SupportsTrunc =) -> int",
              "parameters": [
                {
                  "label": "x"
                }
              ]
            },
            {
              "activeParameter": 0,
              "label": "(x: str | bytes | bytearray, base: SupportsIndex) -> int",
              "parameters": [
                {
                  "label": "x"
                },
                {
                  "label": "base"
                }
              ]
            }
          ]
        }),
    );
}

#[test]
#[serial]
fn check_notebook_cell_change() {
    let server = Project::with_fixture(r#""#).into_server();
    server.open_notebook_with_cells(&["foobar = 1", "\n\nfoobar"]);

    let cell0_uri_str = &server.notebook_cell_uri(0).to_string();
    let pos = TextDocumentPositionParams::new(
        TextDocumentIdentifier {
            uri: server.notebook_cell_uri(1),
        },
        Position::new(2, 0),
    );
    let params = GotoDefinitionParams {
        text_document_position_params: pos,
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
    };

    let expect_result = || {
        server.request_and_expect_json::<GotoDeclaration>(
            params.clone(),
            json!([{
                "targetUri": cell0_uri_str,
                "targetSelectionRange": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 6},
                },
                "targetRange": {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 10},
                },
            }]),
        );
    };

    expect_result();

    server.change_notebook_cell(
        1,
        vec![TextDocumentContentChangeEvent {
            range: Some(Range {
                start: Position {
                    line: 2,
                    character: 0,
                },
                end: Position {
                    line: 2,
                    character: 1,
                },
            }),
            range_length: None,
            text: "".into(),
        }],
    );

    server.request_and_expect_json::<GotoDeclaration>(params.clone(), json!(None::<()>));

    server.change_notebook_cell(
        1,
        vec![TextDocumentContentChangeEvent {
            range: Some(Range {
                start: Position {
                    line: 2,
                    character: 0,
                },
                end: Position {
                    line: 2,
                    character: 0,
                },
            }),
            range_length: None,
            text: "f".into(),
        }],
    );
    expect_result();
}

#[test]
#[serial]
fn test_symbols() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        a: int = 1
        b = ""
        type Alias = int

        class X:
            x: int

            def f(self, param: int) -> None:
                func_var: int = 1

            class Y:
                def g(self, param: int) -> None: ...

        [file bar.py]
        x = 1
        "#,
    )
    .into_server();

    let foo_py = server.doc_id("foo.py").uri;
    let bar_py = server.doc_id("bar.py").uri;

    server.request_and_expect_json::<WorkspaceSymbolRequest>(
        WorkspaceSymbolParams::default(),
        json!([
          {
            "kind": SymbolKind::VARIABLE,
            "location": {
              "range": {
                "end": {
                  "line": 0,
                  "character": 1,
                },
                "start": {
                  "line": 0,
                  "character": 0,
                }
              },
              "uri": bar_py,
            },
            "name": "x"
          },
          {
            "kind": SymbolKind::VARIABLE,
            "location": {
              "range": {
                "end": {
                  "line": 1,
                  "character": 1,
                },
                "start": {
                  "line": 1,
                  "character": 0,
                }
              },
              "uri": foo_py,
            },
            "name": "b"
          },
          {
            "kind": SymbolKind::VARIABLE,
            "location": {
              "range": {
                "end": {
                  "line": 0,
                  "character": 1,
                },
                "start": {
                  "line": 0,
                  "character": 0,
                }
              },
              "uri": foo_py,
            },
            "name": "a"
          },
          {
            "containerName": "X",
            "kind": SymbolKind::FIELD,
            "location": {
              "range": {
                "end": {
                  "line": 5,
                  "character": 5,
                },
                "start": {
                  "line": 5,
                  "character": 4,
                }
              },
              "uri": foo_py,
            },
            "name": "x"
          },
          {
            "containerName": "X.Y",
            "kind": SymbolKind::METHOD,
            "location": {
              "range": {
                "end": {
                  "line": 11,
                  "character": 13,
                },
                "start": {
                  "line": 11,
                  "character": 12,
                }
              },
              "uri": foo_py,
            },
            "name": "g"
          },
          {
            "containerName": "X",
            "kind": SymbolKind::CLASS,
            "location": {
              "range": {
                "end": {
                  "line": 10,
                  "character": 11,
                },
                "start": {
                  "line": 10,
                  "character": 10,
                }
              },
              "uri": foo_py,
            },
            "name": "Y"
          },
          {
            "containerName": "X",
            "kind": SymbolKind::METHOD,
            "location": {
              "range": {
                "end": {
                  "line": 7,
                  "character": 9,
                },
                "start": {
                  "line": 7,
                  "character": 8,
                }
              },
              "uri": foo_py,
            },
            "name": "f"
          },
          {
            "kind": SymbolKind::CLASS,
            "location": {
              "range": {
                "end": {
                  "line": 4,
                  "character": 7,
                },
                "start": {
                  "line": 4,
                  "character": 6,
                }
              },
              "uri": foo_py,
            },
            "name": "X"
          },
          {
            "kind": SymbolKind::INTERFACE,
            "location": {
              "range": {
                "end": {
                  "line": 2,
                  "character": 10,
                },
                "start": {
                  "line": 2,
                  "character": 5,
                }
              },
              "uri": foo_py,
            },
            "name": "Alias"
          }
        ]),
    );

    server.request_and_expect_json::<WorkspaceSymbolRequest>(
        WorkspaceSymbolParams {
            query: "lia".to_string(),
            ..Default::default()
        },
        json!([
            {
              "kind": SymbolKind::INTERFACE,
              "location": {
                "range": {
                  "end": {
                    "line": 2,
                    "character": 10,
                  },
                  "start": {
                    "line": 2,
                    "character": 5,
                  }
                },
                "uri": foo_py,
              },
              "name": "Alias"
            }
        ]),
    );

    server.request_and_expect_json::<DocumentSymbolRequest>(
        DocumentSymbolParams {
            text_document: server.doc_id("foo.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!([
            {
              "kind": SymbolKind::VARIABLE,
              "name": "b",
              "range": {
                "end": {
                  "line": 1,
                  "character": 6,
                },
                "start": {
                  "line": 1,
                  "character": 0,
                }
              },
              "selectionRange": {
                "end": {
                  "line": 1,
                  "character": 1,
                },
                "start": {
                  "line": 1,
                  "character": 0,
                }
              }
            },
            {
              "kind": SymbolKind::VARIABLE,
              "name": "a",
              "range": {
                "end": {
                  "line": 0,
                  "character": 10,
                },
                "start": {
                  "line": 0,
                  "character": 0,
                }
              },
              "selectionRange": {
                "end": {
                  "line": 0,
                  "character": 1,
                },
                "start": {
                  "line": 0,
                  "character": 0,
                }
              }
            },
            {
              "children": [
                {
                  "detail": "X",
                  "kind": SymbolKind::FIELD,
                  "name": "x",
                  "range": {
                    "end": {
                      "line": 5,
                      "character": 10,
                    },
                    "start": {
                      "line": 5,
                      "character": 4,
                    }
                  },
                  "selectionRange": {
                    "end": {
                      "line": 5,
                      "character": 5,
                    },
                    "start": {
                      "line": 5,
                      "character": 4,
                    }
                  }
                },
                {
                  "detail": "X",
                  "kind": SymbolKind::METHOD,
                  "name": "f",
                  "range": {
                    "end": {
                      "line": 10,
                      "character": 4,
                    },
                    "start": {
                      "line": 7,
                      "character": 4,
                    }
                  },
                  "selectionRange": {
                    "end": {
                      "line": 7,
                      "character": 9,
                    },
                    "start": {
                      "line": 7,
                      "character": 8,
                    }
                  }
                },
                {
                  "children": [
                    {
                      "detail": "X.Y",
                      "kind": SymbolKind::METHOD,
                      "name": "g",
                      "range": {
                        "end": {
                          "line": 12,
                          "character": 0,
                        },
                        "start": {
                          "line": 11,
                          "character": 8,
                        }
                      },
                      "selectionRange": {
                        "end": {
                          "line": 11,
                          "character": 13,
                        },
                        "start": {
                          "line": 11,
                          "character": 12,
                        }
                      }
                    }
                  ],
                  "detail": "X",
                  "kind": SymbolKind::CLASS,
                  "name": "Y",
                  "range": {
                    "end": {
                      "line": 13,
                      "character": 0,
                    },
                    "start": {
                      "line": 10,
                      "character": 4,
                    }
                  },
                  "selectionRange": {
                    "end": {
                      "line": 10,
                      "character": 11,
                    },
                    "start": {
                      "line": 10,
                      "character": 10,
                    }
                  }
                }
              ],
              "kind": SymbolKind::CLASS,
              "name": "X",
              "range": {
                "end": {
                  "line": 13,
                  "character": 0,
                },
                "start": {
                  "line": 4,
                  "character": 0,
                }
              },
              "selectionRange": {
                "end": {
                  "line": 4,
                  "character": 7,
                },
                "start": {
                  "line": 4,
                  "character": 6,
                }
              }
            },
            {
              "kind": SymbolKind::INTERFACE,
              "name": "Alias",
              "range": {
                "end": {
                  "line": 2,
                  "character": 16,
                },
                "start": {
                  "line": 2,
                  "character": 0,
                }
              },
              "selectionRange": {
                "end": {
                  "line": 2,
                  "character": 10,
                },
                "start": {
                  "line": 2,
                  "character": 5,
                }
              }
            }
        ]),
    );
    server.request_and_expect_json::<DocumentSymbolRequest>(
        DocumentSymbolParams {
            text_document: server.doc_id("bar.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!([
          {
            "kind": SymbolKind::VARIABLE,
            "name": "x",
            "range": {
              "end": {
                "line": 0,
                "character": 5,
              },
              "start": {
                "line": 0,
                "character": 0,
              }
            },
            "selectionRange": {
              "end": {
                "line": 0,
                "character": 1,
              },
              "start": {
                "line": 0,
                "character": 0,
              }
            }
          }
        ]),
    );
}

#[test]
#[serial]
fn test_semantic_tokens_and_selection_ranges() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        class A:
            @property
            def foo(self): ...
            def f2(self): ...

        A().foo
        "#,
    )
    .into_server();

    let server_capabilites = server.connection.server_capabilities.as_ref().unwrap();
    let legend = match server_capabilites
        .semantic_tokens_provider
        .as_ref()
        .unwrap()
    {
        SemanticTokensServerCapabilities::SemanticTokensOptions(opts) => &opts.legend,
        SemanticTokensServerCapabilities::SemanticTokensRegistrationOptions(..) => unreachable!(),
    };
    let tok_to_u32 = |tok: SemanticTokenType| {
        legend
            .token_types
            .iter()
            .position(|from_server| tok == *from_server)
            .unwrap() as u32
    };

    let json = server
        .connection
        .request_with_expected_response::<SemanticTokensFullRequest>(SemanticTokensParams {
            text_document: server.doc_id("foo.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let tokens = SemanticTokens::deserialize(json).unwrap();
    assert_eq!(
        tokens.data,
        vec![
            SemanticToken {
                delta_line: 0,
                delta_start: 6,
                length: 1,
                token_type: tok_to_u32(SemanticTokenType::CLASS),
                token_modifiers_bitset: 3
            },
            SemanticToken {
                delta_line: 1,
                delta_start: 5,
                length: 8,
                token_type: tok_to_u32(SemanticTokenType::CLASS),
                token_modifiers_bitset: 0
            },
            SemanticToken {
                delta_line: 1,
                delta_start: 8,
                length: 3,
                token_type: tok_to_u32(SemanticTokenType::PROPERTY),
                token_modifiers_bitset: 7
            },
            SemanticToken {
                delta_line: 0,
                delta_start: 4,
                length: 4,
                token_type: tok_to_u32(SemanticTokenType::VARIABLE),
                token_modifiers_bitset: 2
            },
            SemanticToken {
                delta_line: 1,
                delta_start: 8,
                length: 2,
                token_type: tok_to_u32(SemanticTokenType::FUNCTION),
                token_modifiers_bitset: 3
            },
            SemanticToken {
                delta_line: 0,
                delta_start: 3,
                length: 4,
                token_type: tok_to_u32(SemanticTokenType::VARIABLE),
                token_modifiers_bitset: 2
            },
            SemanticToken {
                delta_line: 2,
                delta_start: 0,
                length: 1,
                token_type: tok_to_u32(SemanticTokenType::CLASS),
                token_modifiers_bitset: 0
            },
            SemanticToken {
                delta_line: 0,
                delta_start: 4,
                length: 3,
                token_type: tok_to_u32(SemanticTokenType::PROPERTY),
                token_modifiers_bitset: 4
            }
        ]
    );

    let json = server
        .connection
        .request_with_expected_response::<SemanticTokensRangeRequest>(SemanticTokensRangeParams {
            text_document: server.doc_id("foo.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            range: Range {
                start: Position {
                    line: 2,
                    character: 0,
                },
                end: Position {
                    line: 3,
                    character: 0,
                },
            },
        });
    let tokens = SemanticTokens::deserialize(json).unwrap();
    assert_eq!(
        tokens.data,
        vec![
            SemanticToken {
                delta_line: 2,
                delta_start: 8,
                length: 3,
                token_type: tok_to_u32(SemanticTokenType::PROPERTY),
                token_modifiers_bitset: 7
            },
            SemanticToken {
                delta_line: 0,
                delta_start: 4,
                length: 4,
                token_type: tok_to_u32(SemanticTokenType::VARIABLE),
                token_modifiers_bitset: 2
            }
        ]
    );

    server.request_and_expect_json::<SelectionRangeRequest>(
        SelectionRangeParams {
            text_document: server.doc_id("foo.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
            positions: vec![
                Position {
                    line: 4,
                    character: 0,
                },
                Position {
                    line: 5,
                    character: 7,
                },
            ],
        },
        json!([
          {
            "parent": {
              "parent": {
                "parent": {
                  "range": {
                    "end": {
                      "character": 0,
                      "line": 6
                    },
                    "start": {
                      "character": 0,
                      "line": 0
                    }
                  }
                },
                "range": {
                  "end": {
                    "character": 0,
                    "line": 5
                  },
                  "start": {
                    "character": 0,
                    "line": 0
                  }
                }
              },
              "range": {
                "end": {
                  "character": 0,
                  "line": 4
                },
                "start": {
                  "character": 4,
                  "line": 3
                }
              }
            },
            "range": {
              "end": {
                "character": 0,
                "line": 4
              },
              "start": {
                "character": 21,
                "line": 3
              }
            }
          },
          {
            "parent": {
              "parent": {
                "parent": {
                  "range": {
                    "end": {
                      "character": 0,
                      "line": 6
                    },
                    "start": {
                      "character": 0,
                      "line": 0
                    }
                  }
                },
                "range": {
                  "end": {
                    "character": 0,
                    "line": 6
                  },
                  "start": {
                    "character": 0,
                    "line": 5
                  }
                }
              },
              "range": {
                "end": {
                  "character": 7,
                  "line": 5
                },
                "start": {
                  "character": 0,
                  "line": 5
                }
              }
            },
            "range": {
              "end": {
                "character": 7,
                "line": 5
              },
              "start": {
                "character": 4,
                "line": 5
              }
            }
          }
        ]),
    );
}
