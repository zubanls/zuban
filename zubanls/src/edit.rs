//! Types and utilities for working with text, modifying source files, and `ZubanLS <-> LSP` type conversion.

use lsp_types::PositionEncodingKind;

use crate::PositionEncoding;

use zuban_source_file::LineIndex;
use zuban_source_file::OneIndexed;
use zuban_source_file::{LineIndex, SourceLocation};
use zuban_text_size::{TextRange, TextSize};

pub(crate) type DocumentVersion = i32;

/// A convenient enumeration for supported text encodings. Can be converted to [`lsp_types::PositionEncodingKind`].
// Please maintain the order from least to greatest priority for the derived `Ord` impl.
#[derive(Default, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PositionEncoding {
    /// UTF 16 is the encoding supported by all LSP clients.
    #[default]
    UTF16,

    /// Second choice because UTF32 uses a fixed 4 byte encoding for each character (makes conversion relatively easy)
    UTF32,

    /// Rust analyzer's preferred encoding, because Rust uses utf-8 strings internally
    UTF8,
}

impl From<PositionEncoding> for lsp_types::PositionEncodingKind {
    fn from(value: PositionEncoding) -> Self {
        match value {
            PositionEncoding::UTF8 => lsp_types::PositionEncodingKind::UTF8,
            PositionEncoding::UTF16 => lsp_types::PositionEncodingKind::UTF16,
            PositionEncoding::UTF32 => lsp_types::PositionEncodingKind::UTF32,
        }
    }
}

impl TryFrom<&lsp_types::PositionEncodingKind> for PositionEncoding {
    type Error = ();

    fn try_from(value: &PositionEncodingKind) -> Result<Self, Self::Error> {
        Ok(if value == &PositionEncodingKind::UTF8 {
            PositionEncoding::UTF8
        } else if value == &PositionEncodingKind::UTF16 {
            PositionEncoding::UTF16
        } else if value == &PositionEncodingKind::UTF32 {
            PositionEncoding::UTF32
        } else {
            return Err(());
        })
    }
}

pub(crate) trait RangeExt {
    fn to_text_range(&self, text: &str, index: &LineIndex, encoding: PositionEncoding)
        -> TextRange;
}

pub(crate) trait ToRangeExt {
    fn to_range(
        &self,
        text: &str,
        index: &LineIndex,
        encoding: PositionEncoding,
    ) -> lsp_types::Range;
}

fn u32_index_to_usize(index: u32) -> usize {
    usize::try_from(index).expect("u32 fits in usize")
}

impl RangeExt for lsp_types::Range {
    fn to_text_range(
        &self,
        text: &str,
        index: &LineIndex,
        encoding: PositionEncoding,
    ) -> TextRange {
        let start_line = index.line_range(
            OneIndexed::from_zero_indexed(u32_index_to_usize(self.start.line)),
            text,
        );
        let end_line = index.line_range(
            OneIndexed::from_zero_indexed(u32_index_to_usize(self.end.line)),
            text,
        );

        let (start_column_offset, end_column_offset) = match encoding {
            PositionEncoding::UTF8 => (
                TextSize::new(self.start.character),
                TextSize::new(self.end.character),
            ),

            PositionEncoding::UTF16 => {
                // Fast path for ASCII only documents
                if index.is_ascii() {
                    (
                        TextSize::new(self.start.character),
                        TextSize::new(self.end.character),
                    )
                } else {
                    // UTF16 encodes characters either as one or two 16 bit words.
                    // The position in `range` is the 16-bit word offset from the start of the line (and not the character offset)
                    // UTF-16 with a text that may use variable-length characters.
                    (
                        utf8_column_offset(self.start.character, &text[start_line]),
                        utf8_column_offset(self.end.character, &text[end_line]),
                    )
                }
            }
            PositionEncoding::UTF32 => {
                // UTF-32 uses 4 bytes for each character. Meaning, the position in range is a character offset.
                return TextRange::new(
                    index.offset(
                        OneIndexed::from_zero_indexed(u32_index_to_usize(self.start.line)),
                        OneIndexed::from_zero_indexed(u32_index_to_usize(self.start.character)),
                        text,
                    ),
                    index.offset(
                        OneIndexed::from_zero_indexed(u32_index_to_usize(self.end.line)),
                        OneIndexed::from_zero_indexed(u32_index_to_usize(self.end.character)),
                        text,
                    ),
                );
            }
        };

        TextRange::new(
            start_line.start() + start_column_offset.clamp(TextSize::new(0), start_line.end()),
            end_line.start() + end_column_offset.clamp(TextSize::new(0), end_line.end()),
        )
    }
}

impl ToRangeExt for TextRange {
    fn to_range(
        &self,
        text: &str,
        index: &LineIndex,
        encoding: PositionEncoding,
    ) -> lsp_types::Range {
        lsp_types::Range {
            start: source_location_to_position(&offset_to_source_location(
                self.start(),
                text,
                index,
                encoding,
            )),
            end: source_location_to_position(&offset_to_source_location(
                self.end(),
                text,
                index,
                encoding,
            )),
        }
    }
}

/// Converts a UTF-16 code unit offset for a given line into a UTF-8 column number.
fn utf8_column_offset(utf16_code_unit_offset: u32, line: &str) -> TextSize {
    let mut utf8_code_unit_offset = TextSize::new(0);

    let mut i = 0u32;

    for c in line.chars() {
        if i >= utf16_code_unit_offset {
            break;
        }

        // Count characters encoded as two 16 bit words as 2 characters.
        {
            utf8_code_unit_offset +=
                TextSize::new(u32::try_from(c.len_utf8()).expect("utf8 len always <=4"));
            i += u32::try_from(c.len_utf16()).expect("utf16 len always <=2");
        }
    }

    utf8_code_unit_offset
}

fn offset_to_source_location(
    offset: TextSize,
    text: &str,
    index: &LineIndex,
    encoding: PositionEncoding,
) -> SourceLocation {
    match encoding {
        PositionEncoding::UTF8 => {
            let row = index.line_index(offset);
            let column = offset - index.line_start(row, text);

            SourceLocation {
                column: OneIndexed::from_zero_indexed(column.to_usize()),
                row,
            }
        }
        PositionEncoding::UTF16 => {
            let row = index.line_index(offset);

            let column = if index.is_ascii() {
                (offset - index.line_start(row, text)).to_usize()
            } else {
                let up_to_line = &text[TextRange::new(index.line_start(row, text), offset)];
                up_to_line.encode_utf16().count()
            };

            SourceLocation {
                column: OneIndexed::from_zero_indexed(column),
                row,
            }
        }
        PositionEncoding::UTF32 => index.source_location(offset, text),
    }
}

fn source_location_to_position(location: &SourceLocation) -> lsp_types::Position {
    lsp_types::Position {
        line: u32::try_from(location.row.to_zero_indexed()).expect("row usize fits in u32"),
        character: u32::try_from(location.column.to_zero_indexed())
            .expect("character usize fits in u32"),
    }
}

/// The state of an individual document in the server. Stays up-to-date
/// with changes made by the user, including unsaved changes.
#[derive(Debug, Clone)]
pub(crate) struct TextDocument {
    /// The string contents of the document.
    contents: String,
    /// A computed line index for the document. This should always reflect
    /// the current version of `contents`. Using a function like [`Self::modify`]
    /// will re-calculate the line index automatically when the `contents` value is updated.
    index: LineIndex,
    /// The latest version of the document, set by the LSP client. The server will panic in
    /// debug mode if we attempt to update the document with an 'older' version.
    version: DocumentVersion,
}

impl TextDocument {
    pub fn new(contents: String, version: DocumentVersion) -> Self {
        let index = LineIndex::from_source_text(&contents);
        Self {
            contents,
            index,
            version,
        }
    }

    pub fn into_contents(self) -> String {
        self.contents
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn index(&self) -> &LineIndex {
        &self.index
    }

    pub fn version(&self) -> DocumentVersion {
        self.version
    }

    pub fn apply_changes(
        &mut self,
        changes: Vec<lsp_types::TextDocumentContentChangeEvent>,
        new_version: DocumentVersion,
        encoding: PositionEncoding,
    ) {
        if let [lsp_types::TextDocumentContentChangeEvent {
            range: None, text, ..
        }] = changes.as_slice()
        {
            tracing::debug!("Fast path - replacing entire document");
            self.modify(|contents, version| {
                contents.clone_from(text);
                *version = new_version;
            });
            return;
        }

        let old_contents = self.contents().to_string();
        let mut new_contents = self.contents().to_string();
        let mut active_index = self.index().clone();

        for lsp_types::TextDocumentContentChangeEvent {
            range,
            text: change,
            ..
        } in changes
        {
            if let Some(range) = range {
                let range = range.to_text_range(&new_contents, &active_index, encoding);

                new_contents.replace_range(
                    usize::from(range.start())..usize::from(range.end()),
                    &change,
                );
            } else {
                new_contents = change;
            }

            if new_contents != old_contents {
                active_index = LineIndex::from_source_text(&new_contents);
            }
        }

        self.modify_with_manual_index(|contents, version, index| {
            if contents != &new_contents {
                *index = active_index;
            }
            *contents = new_contents;
            *version = new_version;
        });
    }

    pub fn update_version(&mut self, new_version: DocumentVersion) {
        self.modify_with_manual_index(|_, version, _| {
            *version = new_version;
        });
    }

    // A private function for modifying the document's internal state
    fn modify(&mut self, func: impl FnOnce(&mut String, &mut DocumentVersion)) {
        self.modify_with_manual_index(|c, v, i| {
            func(c, v);
            *i = LineIndex::from_source_text(c);
        });
    }

    // A private function for overriding how we update the line index by default.
    fn modify_with_manual_index(
        &mut self,
        func: impl FnOnce(&mut String, &mut DocumentVersion, &mut LineIndex),
    ) {
        let old_version = self.version;
        func(&mut self.contents, &mut self.version, &mut self.index);
        debug_assert!(self.version >= old_version);
    }
}
