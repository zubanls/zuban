use super::*;


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
                "value": "```python\n(variable) d: Class\n```\n---\ndoc 🫶 love",
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

