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
    CodeActionParams, CompletionItem, CompletionItemKind, CompletionParams,
    DiagnosticServerCapabilities, DocumentDiagnosticParams, DocumentDiagnosticReport,
    DocumentDiagnosticReportResult, DocumentHighlightKind, DocumentHighlightParams,
    DocumentSymbolParams, FoldingRangeParams, GotoDefinitionParams, HoverParams, InlayHintParams,
    NumberOrString, PartialResultParams, Position, PositionEncodingKind, Range, ReferenceContext,
    ReferenceParams, RenameParams, SelectionRangeParams, SemanticToken, SemanticTokenType,
    SemanticTokens, SemanticTokensParams, SemanticTokensRangeParams,
    SemanticTokensServerCapabilities, SignatureHelpParams, SymbolKind,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentPositionParams, Url,
    WorkDoneProgressParams, WorkspaceDiagnosticParams, WorkspaceSymbolParams,
    request::{
        CodeActionRequest, Completion, DocumentDiagnosticRequest, DocumentHighlightRequest,
        DocumentSymbolRequest, FoldingRangeRequest, GotoDeclaration, GotoDefinition,
        GotoImplementation, GotoTypeDefinition, HoverRequest, InlayHintRequest,
        PrepareRenameRequest, References, Rename, ResolveCompletionItem, SelectionRangeRequest,
        SemanticTokensFullRequest, SemanticTokensRangeRequest, SignatureHelpRequest,
        WorkspaceDiagnosticRequest, WorkspaceSymbolRequest,
    },
};

mod connection;
mod custom;
mod support;
mod test_initialization_options;
mod test_diagnostics;
mod test_navigation;
mod test_completion;
mod test_symbols;
mod test_editor_features;
mod test_notebooks;

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
    let response = con.initialize(&["/foo/bar"], None, true, false, false, None);

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
        // This might change in the future.
        assert!(!diagnostics.workspace_diagnostics);
    }
    assert_eq!(response.server_info.expect("server_info").name, "zuban");
    con.shutdown_and_exit()
}

#[test]
#[parallel]
fn request_after_shutdown_is_invalid() {
    let con = Connection::initialized(&["/foo/bar"], None, true, false, false, None);
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
            text_document: TextDocumentIdentifier::new(
                Url::from_str("file://does-not-exist").unwrap(),
            ),
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
    let con = Connection::initialized(&["/foo/bar"], None, true, false, false, None);
    con.notify::<lsp_types::notification::Exit>(());
}

#[test]
#[parallel]
fn test_relative_namespace_import() {
    // From GH #486
    let server = Project::with_fixture(
        r#"
        [file main.py]
        from namespace import x
        x.func
        [file namespace/x.py]
        from .y import func
        [file namespace/y.py]
        def func(): ...

        [file pyproject.toml]
        [tool.zuban]
        mypy_path = [".", "namespace"]
        "#,
    )
    .into_server();
    assert!(server.diagnostics_for_file("namespace/x.py").is_empty());
    assert!(server.diagnostics_for_file("main.py").is_empty());

    let pos =
        TextDocumentPositionParams::new(server.doc_id("namespace/x.py"), Position::new(0, 19));
    let actual = server.request_with_expected_response::<Completion>(CompletionParams {
        text_document_position: pos,
        work_done_progress_params: Default::default(),
        partial_result_params: Default::default(),
        context: None,
    });
    let obj = actual.as_array().expect("array")[0]
        .as_object()
        .expect("object");
    assert_eq!(obj["label"].as_str().expect("label"), "func");
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
                uri: Url::from_str(&format!(
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
    // This is not a valid URI, but a lot of clients seem to do that, so we allow that for now and
    // test it here so LSP clients can do that.
    assert_eq!(d("base/with space.py"), [r#""bytes" not callable"#]);

    // Check random files that don't really make sense
    let check_other_uris = [
        Url::from_str("file:///bar/foo").unwrap(),
        Url::from_str("file://foo").unwrap(),
        Url::from_str("file://").unwrap(),
        Url::from_str("https://www.example.com/foo.py").unwrap(),
        Url::from_str("file:/single_slash").unwrap(),
    ];

    let diags_for_uri = |uri: &Url| {
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
        Url::from_str("file:///bar/foo").unwrap(),
        Url::from_str("https://www.example.com/foo.py").unwrap(),
    ];

    if cfg!(windows) {
        check_other_uris.push(Url::from_str("file:/C:/single_slash").unwrap());
    } else {
        check_other_uris.push(Url::from_str("file:/single_slash").unwrap());
        // Some of these are just really weird on Windows, because these paths don't really exist.
        check_other_uris.push(Url::from_str("file://foo").unwrap());
        check_other_uris.push(Url::from_str("file://").unwrap());
    }

    for uri in &mut check_other_uris {
        server.open_in_memory_file_for_uri(uri.clone(), "import m\n1()");
        let (file, diags) = server.expect_publish_diagnostics_with_uri();
        if uri.authority() == "" {
            // Make sure all uris have an authority, because that's how zubanls returns it.
            *uri = Url::from_str(&uri.as_str().replace("file:/", "file:///")).unwrap();
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
        import simple_symlink_dir3

        assert_type(foo.x, Any)
        assert_type(simple_symlink.x, str)
        assert_type(simple_symlink_dir.x, bytes)
        assert_type(simple_symlink_dir2.x, float)
        assert_type(simple_symlink_dir3.x, float)

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
    server
        .tmp_dir
        .create_symlink_dir("simple_symlink_dir2", "simple_symlink_dir3");
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
fn test_virtual_environment() {
    if fails_too_much_on_linux_and_github_actions() {
        // Somehow this test is failing a bit too often on GitHub, so for now ignore it.
        return;
    }

    let run = || {
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

        server.open_in_memory_file(
            PATH,
            "from foo import foo\nfrom bar import bar\nreveal_type(foo)",
        );

        let revealed_type_int = "Revealed type is \"builtins.int\"";
        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            [revealed_type_int]
        );

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
        let revealed_type_any = "Revealed type is \"Any\"";
        server.rename_file_and_wait(old_path, new_path);
        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            [
                "Cannot find implementation or library stub for module named \"foo\"",
                revealed_type_any,
            ]
        );
        server.rename_file_and_wait(new_path, old_path);
        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            [revealed_type_int]
        );

        tracing::info!("Check if rewriting the file causes an issue now");
        let init = &format!("{old_path}/__init__.py");
        server.write_file_and_wait(init, "\n");
        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            ["Module \"foo\" has no attribute \"foo\"", revealed_type_any],
        );

        tracing::info!("Check adding the code again");
        server.write_file_and_wait(init, "foo = 1");
        let mut result = server.expect_publish_diagnostics_for_file(PATH);
        if cfg!(target_os = "windows") && result.len() > 1 {
            // On Windows events may be duplicated, because there is a Create event for writing
            // and then a modification event.
            result = server.expect_publish_diagnostics_for_file(PATH);
        }
        assert_eq!(result, [revealed_type_int]);

        tracing::info!("Check removing it");
        server.remove_file_and_wait(init);
        assert_eq!(
            server.expect_publish_diagnostics_for_file(PATH),
            ["Module \"foo\" has no attribute \"foo\"", revealed_type_any],
        );

        tracing::info!("Check adding it again");
        server.write_file_and_wait(init, "foo = ''");
        let result = server.expect_publish_diagnostics_for_file(PATH);
        assert_eq!(result, ["Revealed type is \"builtins.str\""]);

        tracing::info!("Check modifying the file");
        server.write_file_and_wait(init, "foo = b''");
        let result = server.expect_publish_diagnostics_for_file(PATH);
        assert_eq!(result, ["Revealed type is \"builtins.bytes\""]);

        tracing::info!("Open the __init__ with different content");
        server.open_in_memory_file(init, "foo = {1}");
        assert!(server.expect_publish_diagnostics_for_file(init).is_empty());
        let result = server.expect_publish_diagnostics_for_file(PATH);
        assert_eq!(result, ["Revealed type is \"builtins.set[builtins.int]\""]);

        // This should not have an influence now, because the file is loaded
        server.write_file_and_wait(init, "foo = (1,)");

        tracing::info!("Change the __init__ in memory file");
        server.change_in_memory_file(init, "foo = [1]");
        assert!(server.expect_publish_diagnostics_for_file(init).is_empty());
        let result = server.expect_publish_diagnostics_for_file(PATH);
        assert_eq!(result, ["Revealed type is \"builtins.list[builtins.int]\""]);

        tracing::info!("Close the __init__ in memory file");
        server.close_in_memory_file(init);
        let result = server.expect_publish_diagnostics_for_file(PATH);
        assert_eq!(
            result,
            ["Revealed type is \"builtins.tuple[builtins.int]\""]
        );
    };

    tracing::info!("set venv information via $VIRTUAL_ENV");
    unsafe { std::env::set_var("VIRTUAL_ENV", "venv") };
    run();
    unsafe { std::env::remove_var("VIRTUAL_ENV") };

    tracing::info!(
        "test_virtual_environment - After unsetting it, there should still be no errors, because the venv is found"
    );
    run();
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
fn test_lsp_root_path_wrong() {
    let server = Project::with_fixture(&format!(
        r#"
        [file pyproject.toml]

        [file inner/__init__.py]

        [file inner/something.py]

        [file inner/other.py]
        from inner import something as x
        import something

        [file outer.py]
        from inner import something as x
        import something
        "#
    ))
    .root("inner")
    .into_server();

    assert_eq!(
        server.diagnostics_for_file("outer.py"),
        ["Cannot find implementation or library stub for module named \"something\""]
    );
    assert_eq!(
        server.diagnostics_for_file("inner/other.py"),
        ["Cannot find implementation or library stub for module named \"something\""]
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
        Vec::<String>::default()
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
