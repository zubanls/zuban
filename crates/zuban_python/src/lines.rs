use std::cell::OnceCell;

use parsa_python_cst::CodeIndex;
use regex::Regex;

use crate::InputPosition;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

#[derive(Clone)]
pub(crate) struct NewlineIndices(OnceCell<Box<[u32]>>);

impl NewlineIndices {
    pub fn new() -> Self {
        Self(OnceCell::new())
    }

    fn lines(&self, code: &str) -> &[u32] {
        self.0.get_or_init(|| {
            let mut v = vec![];
            for m in NEWLINES.find_iter(code) {
                v.push(m.end() as CodeIndex);
            }
            v.into_boxed_slice()
        })
    }

    pub fn line_column_to_byte(
        &self,
        code: &str,
        input: InputPosition,
    ) -> anyhow::Result<CodeIndex> {
        let line_infos = |line| {
            let lines = self.lines(code);
            let Some(next_line_start) = lines.get(line) else {
                if lines.len() == line {
                    return Ok(if lines.is_empty() {
                        (0, code)
                    } else {
                        let start = lines[line - 1];
                        (start, &code[start as usize..])
                    });
                }
                anyhow::bail!(
                    "File has only {} lines, but line {line} is requested",
                    lines.len() + 1
                );
            };
            let start = if line == 0 { 0 } else { lines[line - 1] };
            Ok((start, &code[start as usize..*next_line_start as usize - 1]))
        };

        // TODO Also column can be bigger than the current line. Currently they are rounded down
        Ok(match input {
            InputPosition::NthUTF8Byte(pos) => {
                let byte = pos.min(code.len());
                if !code.is_char_boundary(byte) {
                    anyhow::bail!("{pos} is not a valid char boundary");
                }
                byte as CodeIndex
            }
            InputPosition::Utf8Bytes { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                let out_column = column.min(rest_line.len());

                if !rest_line.is_char_boundary(out_column) {
                    anyhow::bail!(
                        "Column {column} is not a valid char boundary on line {rest_line:?}"
                    );
                }
                //
                start + out_column as CodeIndex
            }
            InputPosition::Utf16CodeUnits { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                start + utf16_to_utf8_byte_offset(rest_line, column)? as CodeIndex
            }
            InputPosition::CodePoints { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                start
                    + rest_line
                        .chars()
                        .take(column)
                        .map(|c| c.len_utf8() as CodeIndex)
                        .sum::<CodeIndex>()
            }
        })
    }

    pub fn position_infos<'code>(
        &self,
        code: &'code str,
        byte_position: CodeIndex,
    ) -> PositionInfos<'code> {
        let lines = self.lines(code);
        let line = lines.partition_point(|&l| l <= byte_position as CodeIndex);
        PositionInfos {
            line,
            code,
            line_offset_in_code: line
                .checked_sub(1)
                .map(|line| lines[line] as usize)
                .unwrap_or(0),
            byte_position: byte_position as usize,
        }
    }
}

fn utf16_to_utf8_byte_offset(s: &str, utf16_pos: usize) -> anyhow::Result<usize> {
    let mut utf16_count = 0;

    for (utf8_idx, c) in s.char_indices() {
        if utf16_count == utf16_pos {
            return Ok(utf8_idx);
        }

        let char_utf16_len = c.len_utf16();
        if utf16_count + char_utf16_len > utf16_pos {
            // Position is in the middle of this char -> invalid
            anyhow::bail!("Column {utf16_pos} is not a valid code unit boundary on line {s:?}",);
        }

        utf16_count += char_utf16_len;
    }
    Ok(s.len())
}

#[derive(Copy, Clone)]
pub struct PositionInfos<'code> {
    line: usize, // zero-based line number
    pub(crate) line_offset_in_code: usize,
    code: &'code str,
    pub byte_position: usize,
}

impl<'code> PositionInfos<'code> {
    // All columns are zero-based
    pub fn utf8_bytes_column(&self) -> usize {
        self.byte_position - self.line_offset_in_code
    }

    pub fn utf16_code_units_column(&self) -> usize {
        self.line_part().encode_utf16().count()
    }

    pub fn code_points_column(&self) -> usize {
        self.line_part().chars().count()
    }

    pub fn line_zero_based(&self) -> usize {
        self.line
    }

    pub fn line_one_based(&self) -> usize {
        self.line + 1
    }

    fn line_part(&self) -> &str {
        &self.code[self.line_offset_in_code..self.byte_position]
    }

    pub(crate) fn code_until(&self, end_pos: PositionInfos) -> &'code str {
        &self.code[self.byte_position..end_pos.byte_position]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_newline_indices_no_line() {
        let indices = NewlineIndices::new();
        let code = "ä";
        assert!(indices.lines(code).is_empty());
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 0, column: 2 })
                .unwrap(),
            2
        );
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 0, column: 3 })
                .unwrap(),
            2
        );
        assert!(indices
            .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 0, column: 1 })
            .is_err());
    }

    #[test]
    fn test_newline_indices_without_ending_newlines() {
        let indices = NewlineIndices::new();
        let code = "x\nä";
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 2 })
                .unwrap(),
            4
        );
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 3 })
                .unwrap(),
            4
        );
        assert!(indices
            .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 1 })
            .is_err());
    }
}
