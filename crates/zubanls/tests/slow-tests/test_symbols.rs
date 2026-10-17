use super::*;

#[test]
#[serial]
fn test_symbols_nested() {
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
fn test_symbols_flat() {
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
    .without_hierarchical_document_symbol_support()
    .into_server();

    let foo_py = server.doc_id("foo.py").uri;
    let bar_py = server.doc_id("bar.py").uri;

    server.request_and_expect_json::<WorkspaceSymbolRequest>(
        WorkspaceSymbolParams::default(),
        json!([
          {
            "kind": 13,
            "location": {
              "range": {
                "end": {
                  "character": 1,
                  "line": 0
                },
                "start": {
                  "character": 0,
                  "line": 0
                }
              },
              "uri": foo_py,
            },
            "name": "a"
          },
          {
            "kind": 11,
            "location": {
              "range": {
                "end": {
                  "character": 10,
                  "line": 2
                },
                "start": {
                  "character": 5,
                  "line": 2
                }
              },
              "uri": foo_py,
            },
            "name": "Alias"
          },
          {
            "containerName": "X",
            "kind": 8,
            "location": {
              "range": {
                "end": {
                  "character": 5,
                  "line": 5
                },
                "start": {
                  "character": 4,
                  "line": 5
                }
              },
              "uri": foo_py,
            },
            "name": "x"
          },
          {
            "containerName": "X.Y",
            "kind": 6,
            "location": {
              "range": {
                "end": {
                  "character": 13,
                  "line": 11
                },
                "start": {
                  "character": 12,
                  "line": 11
                }
              },
              "uri": foo_py,
            },
            "name": "g"
          },
          {
            "containerName": "X",
            "kind": 5,
            "location": {
              "range": {
                "end": {
                  "character": 11,
                  "line": 10
                },
                "start": {
                  "character": 10,
                  "line": 10
                }
              },
              "uri": foo_py,
            },
            "name": "Y"
          },
          {
            "containerName": "X",
            "kind": 6,
            "location": {
              "range": {
                "end": {
                  "character": 9,
                  "line": 7
                },
                "start": {
                  "character": 8,
                  "line": 7
                }
              },
              "uri": foo_py,
            },
            "name": "f"
          },
          {
            "kind": 5,
            "location": {
              "range": {
                "end": {
                  "character": 7,
                  "line": 4
                },
                "start": {
                  "character": 6,
                  "line": 4
                }
              },
              "uri": foo_py,
            },
            "name": "X"
          },
          {
            "kind": 13,
            "location": {
              "range": {
                "end": {
                  "character": 1,
                  "line": 1
                },
                "start": {
                  "character": 0,
                  "line": 1
                }
              },
              "uri": foo_py,
            },
            "name": "b"
          },
          {
            "kind": 13,
            "location": {
              "range": {
                "end": {
                  "character": 1,
                  "line": 0
                },
                "start": {
                  "character": 0,
                  "line": 0
                }
              },
              "uri": bar_py,
            },
            "name": "x"
          }
        ]),
    );

    server.request_and_expect_json::<DocumentSymbolRequest>(
        DocumentSymbolParams {
            text_document: server.doc_id("bar.py"),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        },
        json!([{
          "kind": 13,
          "location": {
            "range": {
              "end": {
                "character": 5,
                "line": 0
              },
              "start": {
                "character": 0,
                "line": 0
              }
            },
            "uri": bar_py,
          },
          "name": "x"
        }]),
    );
}
