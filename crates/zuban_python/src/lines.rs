use std::sync::OnceLock;

use parsa_python_cst::CodeIndex;
use regex::Regex;

use crate::InputPosition;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

pub fn split_lines(code: &str) -> impl Iterator<Item = &str> {
    NEWLINES.split(code)
}

#[derive(Clone)]
pub(crate) struct NewlineIndices(OnceLock<Box<[u32]>>);

impl NewlineIndices {
    pub fn new() -> Self {
        Self(OnceLock::new())
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
    ) -> anyhow::Result<BytePositionInfos> {
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
            let mut line_code = &code[start as usize..*next_line_start as usize - 1];
            if cfg!(windows)
                && let Some(l) = line_code.strip_suffix('\r')
            {
                line_code = l
            }
            Ok((start, line_code))
        };

        Ok(match input {
            InputPosition::NthUTF8Byte(pos) => {
                let byte = pos.min(code.len());
                if !code.is_char_boundary(byte) {
                    anyhow::bail!("{pos} is not a valid char boundary");
                }
                BytePositionInfos {
                    byte: byte as CodeIndex,
                    column_out_of_bounds: byte < pos,
                }
            }
            InputPosition::Utf8Bytes { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                let out_column = column.min(rest_line.len());

                if !rest_line.is_char_boundary(out_column) {
                    anyhow::bail!(
                        "Column {column} is not a valid char boundary on line {rest_line:?}"
                    );
                }
                BytePositionInfos {
                    byte: start + out_column as CodeIndex,
                    column_out_of_bounds: out_column < column,
                }
            }
            InputPosition::Utf16CodeUnits { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                let mut infos = utf16_to_utf8_byte_offset(rest_line, column)?;
                infos.byte += start;
                infos
            }
            InputPosition::CodePoints { line, column } => {
                let (start, rest_line) = line_infos(line)?;
                let byte = start
                    + rest_line
                        .chars()
                        .take(column)
                        .map(|c| c.len_utf8() as CodeIndex)
                        .sum::<CodeIndex>();
                BytePositionInfos {
                    byte,
                    column_out_of_bounds: rest_line.chars().take(column).count() < column,
                }
            }
        })
    }

    pub fn numbers_with_lines<'code>(
        &self,
        code: &'code str,
        skip_n_lines: usize,
    ) -> impl Iterator<Item = (usize, &'code str)> {
        let line_indexes = self.lines(code);
        let mut previous = 0;
        if skip_n_lines != 0 {
            previous = line_indexes
                .get(skip_n_lines - 1)
                .copied()
                .unwrap_or_else(|| line_indexes.len() as CodeIndex) as usize;
        }
        line_indexes
            .iter()
            .copied()
            .chain(
                if let Some(last) = line_indexes.last() {
                    (*last as usize != code.len()).then(|| code.len() as CodeIndex + 1)
                } else {
                    Some(code.len() as CodeIndex + 1)
                }
                .into_iter(),
            )
            .enumerate()
            .skip(skip_n_lines)
            .map(move |(line_nr, line_index)| {
                let line_index = line_index as usize;
                let Some(mut result) = code.get(previous..line_index - 1) else {
                    panic!("Wanted to access {previous}..{line_index} for code {code:?}");
                };
                if cfg!(windows)
                    && let Some(l) = result.strip_suffix('\r')
                {
                    result = l
                }
                previous = line_index;
                (line_nr, result)
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

fn utf16_to_utf8_byte_offset(s: &str, utf16_pos: usize) -> anyhow::Result<BytePositionInfos> {
    let mut utf16_count = 0;

    let mut char_indices_counter = 0;
    for (utf8_idx, c) in s.char_indices() {
        char_indices_counter += 1;
        if utf16_count == utf16_pos {
            return Ok(BytePositionInfos {
                byte: utf8_idx as CodeIndex,
                column_out_of_bounds: false,
            });
        }

        let char_utf16_len = c.len_utf16();
        if utf16_count + char_utf16_len > utf16_pos {
            // Position is in the middle of this char -> invalid
            anyhow::bail!("Column {utf16_pos} is not a valid code unit boundary on line {s:?}",);
        }

        utf16_count += char_utf16_len;
    }
    Ok(BytePositionInfos {
        byte: s.len() as CodeIndex,
        column_out_of_bounds: utf16_pos > char_indices_counter,
    })
}

pub(crate) struct BytePositionInfos {
    pub byte: CodeIndex,
    pub column_out_of_bounds: bool,
}

#[derive(Copy, Clone, Debug)]
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
                .unwrap()
                .byte,
            2
        );
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 0, column: 3 })
                .unwrap()
                .byte,
            2
        );
        assert!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 0, column: 1 })
                .is_err()
        );
    }

    #[test]
    fn test_newline_indices_without_ending_newlines() {
        let indices = NewlineIndices::new();
        let code = "x\nä";
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 2 })
                .unwrap()
                .byte,
            4
        );
        assert_eq!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 3 })
                .unwrap()
                .byte,
            4
        );
        assert!(
            indices
                .line_column_to_byte(code, InputPosition::Utf8Bytes { line: 1, column: 1 })
                .is_err()
        );
    }

    #[test]
    fn test_numbers_with_lines() {
        let check = |code, skip_lines| {
            let indices = NewlineIndices::new();
            indices
                .numbers_with_lines(code, skip_lines)
                .collect::<Vec<_>>()
        };
        let c1 = "x\nä\ny";
        assert_eq!(check(c1, 0), [(0, "x"), (1, "ä"), (2, "y")]);
        assert_eq!(check(c1, 1), [(1, "ä"), (2, "y")]);
        assert_eq!(check(c1, 2), [(2, "y")]);
        assert_eq!(check(c1, 3), []);
        assert_eq!(check(c1, 4), []);

        let c2 = "x\ny\n";
        assert_eq!(check(c2, 0), [(0, "x"), (1, "y")]);
        assert_eq!(check(c2, 1), [(1, "y")]);
        assert_eq!(check(c2, 2), []);
        assert_eq!(check(c2, 3), []);

        let c3 = "x\n";
        assert_eq!(check(c3, 0), [(0, "x")]);
        assert_eq!(check(c3, 1), []);
        assert_eq!(check(c3, 2), []);

        let c4 = "x";
        //assert_eq!(check(c4, 0), [(0, "x")]);
        assert_eq!(check(c4, 1), []);
        assert_eq!(check(c4, 2), []);

        let c5 = "";
        assert_eq!(check(c5, 0), [(0, "")]);
        assert_eq!(check(c5, 1), []);
        assert_eq!(check(c5, 2), []);
    }
}
