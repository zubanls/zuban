use std::cell::OnceCell;

use parsa_python_cst::CodeIndex;
use regex::Regex;

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
            // TODO probably use a OnceCell or something
            let mut v = vec![];
            for m in NEWLINES.find_iter(code) {
                v.push(m.end() as CodeIndex);
            }
            v.into_boxed_slice()
        })
    }

    pub fn line_column_to_byte(&self, code: &str, line: usize, column: usize) -> CodeIndex {
        if line == 0 {
            return column as CodeIndex;
        }

        let byte = self.lines(code)[line - 1];
        // TODO column can be unicode, is that an issue?
        // TODO Also column can be bigger than the current line.
        byte + column as CodeIndex
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

#[derive(Copy, Clone)]
pub struct PositionInfos<'code> {
    line: usize, // zero-based line number
    pub line_offset_in_code: usize,
    code: &'code str,
    pub byte_position: usize,
}

impl<'code> PositionInfos<'code> {
    // All columns are zero-based
    pub fn utf8_bytes_column(&self) -> usize {
        self.byte_position - self.line_offset_in_code
    }

    pub fn utf16_bytes_column(&self) -> usize {
        self.line_part().encode_utf16().count() * 2
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
