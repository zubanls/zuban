use super::*;


#[test]
#[serial]
fn diagnostics_for_saved_files_and_workspace_diagnostics() {
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
                  "source": "zuban"
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
                  "source": "zuban"
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

    server.request_and_expect_json::<WorkspaceDiagnosticRequest>(
        WorkspaceDiagnosticParams {
            identifier: None,
            previous_result_ids: vec![],
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!({
          "items": [
            {
              "items": [
                {
                  "code": "name-defined",
                  "message": "Name \"lala\" is not defined",
                  "range": {
                    "end": {
                      "line": 1,
                      "character": 4,
                    },
                    "start": {
                      "line": 1,
                      "character": 0,
                    }
                  },
                  "severity": 1,
                  "source": "zuban"
                }
              ],
              "kind": "full",
              "uri": server.doc_id("pkg/foo.py").uri,
              "version": null
            },
            {
              "items": [
                {
                  "code": "attr-defined",
                  "message": "Module \"pkg.foo\" has no attribute \"Bar\"",
                  "range": {
                    "end": {
                      "line": 1,
                      "character": 23,
                    },
                    "start": {
                      "line": 1,
                      "character": 20,
                    }
                  },
                  "severity": 1,
                  "source": "zuban"
                },
                {
                  "code": "operator",
                  "message": "\"int\" not callable",
                  "range": {
                    "end": {
                      "line": 3,
                      "character": 3,
                    },
                    "start": {
                      "line": 3,
                      "character": 0,
                    }
                  },
                  "severity": 1,
                  "source": "zuban"
                }
              ],
              "kind": "full",
              "uri": server.doc_id("pkg/__init__.py").uri,
              "version": null
            }
          ],
        }),
    );
}


#[test]
#[serial]
fn diagnostics_for_protocols_invalidation() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]

        [file foo.py]
        from typing import Protocol
        from other import Alias

        class P(Protocol):
            x: int
        class C:
            x: Alias

        p: P = C()

        [file other.py]
        Alias = int
        "#,
    )
    .into_server();

    server.request_and_expect_json::<DocumentDiagnosticRequest>(
        DocumentDiagnosticParams {
            text_document: server.doc_id("foo.py"),
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
        json!({
            "items": [],
            "kind": "full"
        }),
    );

    // Change if the protocol matches
    server.write_file_and_wait("other.py", "Alias = str\n");

    server.request_and_expect_json::<DocumentDiagnosticRequest>(
        DocumentDiagnosticParams {
            text_document: server.doc_id("foo.py"),
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        },
        json!({
            "items": [
              {
                "code": "assignment",
                "message": "Incompatible types in assignment (expression has type \"C\", variable has type \"P\")",
                "range": {
                  "end": {
                    "character": 10,
                    "line": 8
                  },
                  "start": {
                    "character": 7,
                    "line": 8
                  }
                },
                "severity": 1,
                "source": "zuban"
              },
              {
                "code": "note",
                "message": "Following member(s) of \"C\" have conflicts:",
                "range": {
                  "end": {
                    "character": 10,
                    "line": 8
                  },
                  "start": {
                    "character": 7,
                    "line": 8
                  }
                },
                "severity": 3,
                "source": "zuban"
              },
              {
                "code": "note",
                "message": "    x: expected \"int\", got \"str\"",
                "range": {
                  "end": {
                    "character": 10,
                    "line": 8
                  },
                  "start": {
                    "character": 7,
                    "line": 8
                  }
                },
                "severity": 3,
                "source": "zuban"
              }
            ],
            "kind": "full"
        }),
    );
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
fn pull_notifications_and_refresh_notification() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        [file unrelated.py]

        [file outside_workdir.py]
        import foo

        "#,
    )
    .with_refresh_support()
    .into_server();

    const NO_FOO: &str = "Cannot find implementation or library stub for module named \"foo\"";

    server.open_in_memory_file("in_mem.py", "import foo");

    assert!(server.diagnostics_for_file("in_mem.py").is_empty());

    server.remove_file_and_wait("foo.py");
    server.expect_refreshes();

    assert_eq!(server.diagnostics_for_file("in_mem.py"), [NO_FOO]);

    // This should not cause refreshes, because unrelated is not used in memory files
    server.remove_file_and_wait("unrelated.py");
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
fn check_panic_recovery_without_push() {
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

