use std::borrow::Cow;

use anyhow::bail;
use lsp_types::{Position, TextDocumentContentChangeEvent};

use crate::{InputPosition, lines::NewlineIndices};

pub(crate) fn apply_document_changes(
    file_contents: &str,
    line_indices: &NewlineIndices,
    mut content_changes: Vec<TextDocumentContentChangeEvent>,
    to_input_position: impl Fn(Position) -> InputPosition,
) -> anyhow::Result<String> {
    // If at least one of the changes is a full document change, use the last
    // of them as the starting point and ignore all previous changes.
    let (mut text, content_changes) = match content_changes
        .iter()
        .rposition(|change| change.range.is_none())
    {
        Some(idx) => {
            let text = std::mem::take(&mut content_changes[idx].text);
            (text, &content_changes[idx + 1..])
        }
        None => (file_contents.to_string(), &content_changes[..]),
    };
    if content_changes.is_empty() {
        return Ok(text);
    }

    let mut line_indices = Cow::Borrowed(line_indices);
    // The changes we got must be applied sequentially, but can cross lines so we
    // have to keep our line index updated.
    // Some clients (e.g. Code) sort the ranges in reverse. As an optimization, we
    // remember the last valid line in the index and only rebuild it if needed.
    // The VFS will normalize the end of lines to `\n`.
    let mut index_valid = !0u32;
    for change in content_changes {
        // The None case can't happen as we have handled it above already
        if let Some(range) = change.range {
            if range.start > range.end {
                bail!("Invalid range of a change, start is bigger than end: {range:?}");
            }
            if range.end.line >= index_valid {
                line_indices = Cow::Owned(NewlineIndices::new());
            }
            index_valid = range.start.line;
            let start =
                line_indices.line_column_to_safe_byte(&text, to_input_position(range.start))?;
            let end = line_indices.line_column_to_safe_byte(&text, to_input_position(range.end))?;
            text.replace_range(start as usize..end as usize, &change.text);
        }
    }
    Ok(text)
}

#[cfg(test)]
mod tests {
    use lsp_types::Range;

    use super::*;

    fn simplified_apply_document_changes(
        file_contents: &str,
        change: Vec<TextDocumentContentChangeEvent>,
    ) -> anyhow::Result<String> {
        apply_document_changes(file_contents, &NewlineIndices::new(), change, |pos| {
            InputPosition::CodePoints {
                line: pos.line as usize,
                column: pos.character as usize,
            }
        })
    }

    fn expect_valid_apply_document_change(
        code: &str,
        change: TextDocumentContentChangeEvent,
    ) -> String {
        simplified_apply_document_changes(code, vec![change]).unwrap()
    }

    fn change(
        start_line: u32,
        start_column: u32,
        end_line: u32,
        end_column: u32,
        new_text: &str,
    ) -> TextDocumentContentChangeEvent {
        TextDocumentContentChangeEvent {
            range: Some(Range {
                start: Position {
                    line: start_line,
                    character: start_column,
                },
                end: Position {
                    line: end_line,
                    character: end_column,
                },
            }),
            range_length: None,
            text: new_text.into(),
        }
    }

    #[test]
    fn test_apply_change_valid() {
        assert_eq!(
            expect_valid_apply_document_change("", change(0, 0, 0, 0, "hello")),
            "hello"
        );
        assert_eq!(
            expect_valid_apply_document_change("x\ny\n", change(0, 0, 0, 0, "hello")),
            "hellox\ny\n"
        );
        assert_eq!(
            expect_valid_apply_document_change("x\ndeletethis\n", change(1, 0, 2, 0, "")),
            "x\n"
        );
    }

    #[test]
    fn test_apply_change_unicode() {
        assert_eq!(
            expect_valid_apply_document_change("äöü", change(0, 1, 0, 2, "hello")),
            "ähelloü"
        );
    }

    #[test]
    fn test_apply_change_with_empty() {
        let empty = |new_text: &str| TextDocumentContentChangeEvent {
            range: None,
            range_length: None,
            text: new_text.into(),
        };
        assert_eq!(
            simplified_apply_document_changes("asdf\nb", vec![empty("")]).unwrap(),
            ""
        );
        assert_eq!(
            simplified_apply_document_changes(
                "asdf\nb",
                vec![
                    change(0, 0, 0, 0, "something"),
                    empty("new_code"),
                    change(0, 3, 0, 4, "-")
                ]
            )
            .unwrap(),
            "new-code"
        );
    }

    #[test]
    fn test_apply_change_out_of_bounds() {
        assert_eq!(
            simplified_apply_document_changes(
                "asdf\nb",
                vec![change(0, 0, 0, 0, ""), change(0, 4, 0, 5, "-")]
            )
            .unwrap_err()
            .to_string(),
            "Columns are out of bounds"
        );
        assert_eq!(
            simplified_apply_document_changes("asdf\n", vec![change(2, 0, 2, 0, "x")])
                .unwrap_err()
                .to_string(),
            "File has only 3 lines, but line 2 is requested"
        );
    }

    #[test]
    fn test_apply_change_invalid_reverse() {
        assert_eq!(
            simplified_apply_document_changes("x\n", vec![change(0, 1, 0, 0, "")])
                .unwrap_err()
                .to_string(),
            "Invalid range of a change, start is bigger than end: Range \
             { start: Position { line: 0, character: 1 }, end: Position { line: 0, character: 0 } }"
        );
        assert_eq!(
            simplified_apply_document_changes("x\n", vec![change(1, 0, 0, 1, "")])
                .unwrap_err()
                .to_string(),
            "Invalid range of a change, start is bigger than end: Range \
             { start: Position { line: 1, character: 0 }, end: Position { line: 0, character: 1 } }"
        );
    }
}
