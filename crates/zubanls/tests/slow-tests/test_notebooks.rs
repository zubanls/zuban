use super::*;


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

