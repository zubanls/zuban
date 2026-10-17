use crate::support::Project;
use lsp_types::{
    FoldingRangeParams, InlayHintParams, Position, Range, SelectionRangeParams, SemanticToken,
    SemanticTokenType, SemanticTokens, SemanticTokensParams, SemanticTokensRangeParams,
    SemanticTokensServerCapabilities,
    request::{
        FoldingRangeRequest, InlayHintRequest, SelectionRangeRequest, SemanticTokensFullRequest,
        SemanticTokensRangeRequest,
    },
};
use serde::Deserialize as _;
use serde_json::json;
use serial_test::serial;

#[test]
#[serial]
fn test_semantic_tokens_folding_and_selection_ranges() {
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

    server.request_and_expect_json::<FoldingRangeRequest>(
        FoldingRangeParams {
            text_document: server.doc_id("foo.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!([
          {
            "startLine": 0,
            "startCharacter": 8,
            "endLine": 3,
            "endCharacter": 21,
            "kind": "region",
          }
        ]),
    );
}

#[test]
#[serial]
fn semantic_tokens_after_deleting_open_imported_file_does_not_crash() {
    let server = Project::with_fixture(
        r#"
        [file src/a.py]
        from src.data.b import PREFIXES

        [file src/data/b.py]
        PREFIXES = (
            'a',
        )
        "#,
    )
    .into_server();

    server.open_in_memory_file("src/a.py", "from src.data.b import PREFIXES\n");
    server.open_in_memory_file("src/data/b.py", "PREFIXES = (\n    'a',\n)\n");

    let request_semantic_tokens = |path| {
        server
            .connection
            .request_with_expected_response::<SemanticTokensFullRequest>(SemanticTokensParams {
                text_document: server.doc_id(path),
                work_done_progress_params: Default::default(),
                partial_result_params: Default::default(),
            })
    };
    request_semantic_tokens("src/a.py");
    request_semantic_tokens("src/data/b.py");

    server.remove_file_and_wait("src/data/b.py");
    server.remove_dir_and_wait("src/data");

    request_semantic_tokens("src/a.py");
}

#[test]
#[serial]
fn test_inlay_hints() {
    let server = Project::with_fixture(
        r#"
        [file foo.py]
        before = [1]
        a = 1
        b = int()
        c = a
        d = [1]
        def foo(): return ""

        after = [1]
        "#,
    )
    .into_server();

    server.request_and_expect_json::<InlayHintRequest>(
        InlayHintParams {
            work_done_progress_params: Default::default(),
            text_document: server.doc_id("foo.py"),
            range: Range::new(Position::new(1, 0), Position::new(6, 0)),
        },
        json!([
          {
            "kind": 1,
            "label": ": int",
            "position": {
              "line": 3,
              "character": 1,
            },
            "textEdits": [
              {
                "newText": ": int",
                "range": {
                  "end": {
                    "line": 3,
                    "character": 1,
                  },
                  "start": {
                    "line": 3,
                    "character": 1,
                  }
                }
              }
            ],
          },
          {
            "kind": 1,
            "label": ": list[int]",
            "position": {
              "line": 4,
              "character": 1,
            },
            "textEdits": [
              {
                "newText": ": list[int]",
                "range": {
                  "end": {
                    "line": 4,
                    "character": 1,
                  },
                  "start": {
                    "line": 4,
                    "character": 1,
                  }
                }
              }
            ],
          },
          {
            "kind": 1,
            "label": " -> str",
            "position": {
              "line": 5,
              "character": 9,
            },
            "textEdits": [
              {
                "newText": " -> str",
                "range": {
                  "end": {
                    "line": 5,
                    "character": 9,
                  },
                  "start": {
                    "line": 5,
                    "character": 9,
                  }
                }
              }
            ],
          }
        ]),
    );
}
