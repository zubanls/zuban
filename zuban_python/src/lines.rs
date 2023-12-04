use std::cell::OnceCell;

use parsa_python_ast::CodeIndex;
use regex::Regex;

lazy_static::lazy_static! {
    static ref NEWLINES: Regex = Regex::new(r"\n|\r\n|\r").unwrap();
}

pub struct NewlineIndices(OnceCell<Box<[u32]>>);

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
            panic!("Lines are 1-based")
        } else if line == 1 {
            return column as CodeIndex;
        }

        let byte = self.lines(code)[line - 2];
        // TODO column can be unicode, is that an issue?
        // TODO Also column can be bigger than the current line.
        byte + column as CodeIndex
    }

    pub fn byte_to_line_column(&self, code: &str, byte: CodeIndex) -> (usize, usize) {
        let lines = self.lines(code);
        let line = lines.partition_point(|&l| l <= byte as CodeIndex);
        if line == 0 {
            (line + 1, byte as usize + 1)
        } else {
            (line + 1, (byte - lines[line - 1] + 1) as usize)
        }
    }
}
