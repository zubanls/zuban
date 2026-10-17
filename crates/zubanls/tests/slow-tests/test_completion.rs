use crate::support::Project;
use lsp_types::{
    CodeActionParams, CompletionItem, CompletionItemKind, CompletionParams, Position, Range,
    SignatureHelpParams, TextDocumentPositionParams,
    request::{CodeActionRequest, Completion, ResolveCompletionItem, SignatureHelpRequest},
};
use serde_json::json;
use serial_test::serial;

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
    let result = server.request_and_expect_json::<Completion>(
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
            "label": "__annotate__",
            "sortText": "00002",
            "textEdit": {
              "newText": "__annotate__",
              "range": {
                "start": {
                  "character": 2,
                  "line": 1
                },
                "end": {
                  "character": 4,
                  "line": 1
                },
              }
            }
          },
          {
            "kind": CompletionItemKind::FIELD,
            "label": "__annotations__",
            "sortText": "00003",
            "textEdit": {
              "newText": "__annotations__",
              "range": {
                "start": {
                  "character": 2,
                  "line": 1
                },
                "end": {
                  "character": 4,
                  "line": 1
                },
              }
            }
          },
          {
            "kind": CompletionItemKind::PROPERTY,
            "label": "__dict__",
            "sortText": "00004",
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
            "sortText": "00005",
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
            "sortText": "00006",
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
            "sortText": "00007",
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
            "sortText": "00008",
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
            "sortText": "00009",
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
            "sortText": "0000a",
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

    let first: CompletionItem = serde_json::from_value(result[0].clone()).unwrap();
    server.request_and_expect_json::<ResolveCompletionItem>(
        first,
        json!({
          "documentation": {
            "kind": "markdown",
            "value": "doc 🫶 love"
          },
          "kind": CompletionItemKind::CLASS,
          "label": "MyClass",
          "sortText": "00000",
          "textEdit": {
            "newText": "MyClass",
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
        }),
    );
    let second: CompletionItem = serde_json::from_value(result[1].clone()).unwrap();
    server.request_and_expect_json::<ResolveCompletionItem>(
        second,
        json!({
          "kind": CompletionItemKind::FUNCTION,
          "label": "my_func",
          "sortText": "00001",
          "textEdit": {
            "newText": "my_func",
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
        }),
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
              "label": "(x: str | Buffer | SupportsInt | SupportsIndex =) -> int",
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
fn test_auto_imports_code_actions() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        import types
        MIMEMessage
        "#,
    )
    .into_server();

    let foo = server.doc_id("foo.py");
    server.request_and_expect_json::<CodeActionRequest>(
        CodeActionParams {
            text_document: foo.clone(),
            range: Range::new(Position::new(1, 1), Position::new(1, 3)),
            context: Default::default(),
            partial_result_params: Default::default(),
            work_done_progress_params: Default::default(),
        },
        json!([
            {
            "edit": {
              "changes": {
                foo.uri.as_str(): [
                  {
                    "newText": "from email.mime.message import MIMEMessage\n\n",
                    "range": {
                      "start": {
                        "line": 1,
                        "character": 0,
                      },
                      "end": {
                        "line": 1,
                        "character": 0,
                      },
                    }
                  }
                ]
              }
            },
            "kind": "quickfix",
            "title": "Import `email.mime.message.MIMEMessage`"
          },
          {
            "edit": {
              "changes": {
                foo.uri.as_str(): [
                  {
                    "newText": "  # type: ignore[name-defined]",
                    "range": {
                      "end": {
                        "character": 11,
                        "line": 1
                      },
                      "start": {
                        "character": 11,
                        "line": 1
                      }
                    }
                  }
                ]
              }
            },
            "kind": "quickfix",
            "title": "Add \"# type: ignore[name-defined]\""
          },
          {
            "edit": {
              "changes": {
                foo.uri.as_str(): [
                  {
                    "newText": "  # zuban: ignore[name-defined]",
                    "range": {
                      "end": {
                        "character": 11,
                        "line": 1
                      },
                      "start": {
                        "character": 11,
                        "line": 1
                      }
                    }
                  }
                ]
              }
            },
            "kind": "quickfix",
            "title": "Add \"# zuban: ignore[name-defined]\""
          },
        ]),
    );
}
