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
    request::DocumentDiagnosticRequest, DiagnosticServerCapabilities, DocumentDiagnosticParams,
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, NumberOrString, PartialResultParams,
    PositionEncodingKind, TextDocumentIdentifier, Uri, WorkDoneProgressParams,
};

mod connection;
mod support;

use connection::Connection;
use serde_json::json;
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
#[parallel]
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
    if cfg!(target_os = "linux") && std::env::var("GITHUB_ACTIONS").ok().as_deref() == Some("true")
    {
        // Somehow this test is failing a bit too often on GitHub, so for now ignore it.
        return;
    }
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
#[parallel]
fn check_rename_without_symlinks() {
    check_rename(false);
}

#[test]
#[parallel]
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
    assert!(server
        .expect_publish_diagnostics_for_file("outside_in_mem.py")
        .is_empty());

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
#[cfg(not(windows))] // windows requires elevated permissions to create symlinks
fn symlink_dir_loop() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        from nested import foo
        from nested.nested import foo as bar

        reveal_type(foo.x)

        x = 3
        "#,
    )
    .into_server();

    let cannot_find =
        |name| format!(r#"Cannot find implementation or library stub for module named "{name}""#);

    let d = || server.diagnostics_for_file("foo.py");

    assert_eq!(
        d(),
        vec![
            cannot_find("nested"),
            cannot_find("nested"),
            "Revealed type is \"Any\"".to_string()
        ]
    );

    server.create_symlink_dir_and_wait(".", "nested");

    assert_eq!(
        d(),
        vec![
            cannot_find("nested"),
            cannot_find("nested"),
            "Revealed type is \"Any\"".to_string()
        ]
    );
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
    .into_server_detailed(None);

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
    .into_server_detailed(None);

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
    assert!(server
        .expect_publish_diagnostics_for_file("in_mem.py")
        .is_empty());
}

#[test]
#[serial]
fn publish_diagnostics() {
    // Check PublishDiagnostics where the client is not requesting diagnostics, but receiving them
    // each time a change is made
    let server = Project::with_fixture(
        r#"
            [file exists_in_fs.py]
            [file unrelated.py]
            "#,
    )
    .with_push_diagnostics()
    .into_server();

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

#[test]
#[serial]
fn test_virtual_environment() {
    let run = |expected_first: &[String], expected_second: Option<&[String]>| {
        let server = Project::with_fixture(
            r#"
        [file venv/bin/python]

        [file venv/lib/python3.12/site-packages/foo/__init__.py]
        foo = 1

        [file venv/lib/python3.12/site-packages/foo/py.typed]

        [file venv/lib/python3.12/site-packages/bar.py]
        bar = ''
        1()
        "#,
        )
        .with_push_diagnostics()
        .into_server();

        const PATH: &str = "check.py";

        server.open_in_memory_file(PATH, "from foo import foo\nfrom bar import bar");

        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            expected_first,
        );

        if let Some(expected_second) = expected_second {
            // Remove it by renaming it
            let old_path = "venv/lib/python3.12/site-packages/foo";
            let new_path = "venv/lib/python3.12/site-packages/foo_new";
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

            // Check if rewriting the file causes an issue now
            let init = &format!("{old_path}/__init__.py");
            server.write_file_and_wait(init, "");
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                ["Module \"foo\" has no attribute \"foo\"".to_string()],
            );

            // Check adding the code again
            server.write_file_and_wait(init, "foo = 1");
            let result = server.expect_publish_diagnostics_for_file(PATH);
            assert!(result.is_empty(), "{result:?}");

            // Check removing it
            server.remove_file_and_wait(init);
            assert_eq!(
                server.expect_publish_diagnostics_for_file(PATH),
                ["Module \"foo\" has no attribute \"foo\"".to_string()],
            );

            // Check adding it again
            server.write_file_and_wait(init, "foo = 1");
            assert!(server.expect_publish_diagnostics_for_file(PATH).is_empty());
        } else {
            // There is no watch on the venv dir if the environment variable is not set. Therefore
            // we cannot wait for an event. So we simply remove it.
            server
                .tmp_dir
                .remove_file("venv/lib/python3.12/site-packages/foo/__init__.py")
        }
    };

    let import_err = |name: &str| {
        format!("Cannot find implementation or library stub for module named \"{name}\"")
    };

    // set venv information via $VIRTUAL_ENV
    std::env::set_var("VIRTUAL_ENV", "venv");
    run(&[], Some(&[import_err("foo")]));
    std::env::remove_var("VIRTUAL_ENV");
    // After unsetting it, there should just be errors
    run(&[import_err("foo"), import_err("bar")], None);
}
