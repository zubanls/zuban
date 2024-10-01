use parsa_python::{
    CodeIndex, NonterminalType::fstring, PyNode, PyNodeType::Nonterminal, SiblingIterator,
};

#[derive(Debug)]
pub enum PythonString<'db> {
    Ref(CodeIndex, &'db str),
    String(CodeIndex, String),
    FString,
}

impl<'db> PythonString<'db> {
    pub fn new(strings: SiblingIterator<'db>) -> Self {
        let mut result: Option<Self> = None;
        for literal in strings {
            result = Some(match result {
                Some(s) => s.union(Self::from_literal(literal)),
                None => Self::from_literal(literal),
            });
        }
        result.unwrap()
    }

    pub fn from_literal(literal: PyNode<'db>) -> Self {
        if literal.is_type(Nonterminal(fstring)) {
            Self::FString
        } else {
            let code = literal.as_code();
            let UnpackedLiteral {
                inner,
                inner_start_offset,
                had_raw_modifier,
            } = unpack_string_or_bytes_content(code);
            if had_raw_modifier {
                return Self::Ref(literal.start() + inner_start_offset, inner);
            }

            let mut iterator = inner.as_bytes().iter().enumerate().peekable();
            let mut string = None;
            let mut previous_insert = 0;
            while let Some((i, ch)) = iterator.next() {
                if ch == &b'\\' {
                    if string.is_none() {
                        string = Some(String::with_capacity(inner.len()));
                    }
                    let s = string.as_mut().unwrap();
                    s.push_str(&inner[previous_insert..i]);
                    let (next_index, ch) = iterator.next().unwrap();

                    match ch {
                        b'\\' | b'\'' | b'"' => s.push(*ch as char),
                        b'\n' => (), // Escaping a newline ignores it
                        b'u' => {
                            if let Some(c) = parse_hex(4, iterator.by_ref()) {
                                s.push(c)
                            }
                        }
                        b'U' => {
                            if let Some(c) = parse_hex(8, iterator.by_ref()) {
                                s.push(c)
                            }
                        }
                        b'x' => {
                            if let Some(c) = parse_hex(2, iterator.by_ref()) {
                                s.push(c)
                            }
                        }
                        b'N' => todo!("Need to implement \\N{{...}}"),
                        b'a' => s.push('\x07'), // Bell
                        b'b' => s.push('\x08'), // Backspace
                        b't' => s.push('\x09'), // Tab
                        b'n' => s.push('\n'),   // Newline (line feed \x0a)
                        b'v' => s.push('\x0b'), // Vertical tab
                        b'f' => s.push('\x0c'), // Form Feed
                        b'r' => s.push('\x0d'), // Carriage Return
                        _ => {
                            let string_from_here = &inner[next_index..];
                            if let Some((len, octal)) =
                                parse_python_octal(string_from_here.as_bytes())
                            {
                                for _ in 1..len {
                                    iterator.next();
                                }
                                s.push(octal)
                            } else {
                                s.push('\\');
                                let c = string_from_here.chars().next().unwrap();
                                for _ in 1..c.len_utf8() {
                                    iterator.next();
                                }
                                s.push(c);
                            }
                        }
                    }
                    previous_insert = iterator.peek().map(|x| x.0).unwrap_or_else(|| inner.len());
                }
            }
            if let Some(mut string) = string {
                string.push_str(&inner[previous_insert..inner.len()]);
                Self::String(literal.start() + inner_start_offset, string)
            } else {
                Self::Ref(literal.start() + inner_start_offset, inner)
            }
        }
    }

    fn union(self, other: Self) -> Self {
        match other {
            Self::Ref(start, s2) => match self {
                Self::Ref(_, s1) => Self::String(start, s1.to_owned() + s2),
                Self::String(_, s1) => Self::String(start, s1 + s2),
                Self::FString => Self::FString,
            },
            Self::String(start, s2) => match self {
                Self::Ref(_, s1) => Self::String(start, s1.to_owned() + &s2),
                Self::String(_, s1) => Self::String(start, s1 + &s2),
                Self::FString => Self::FString,
            },
            Self::FString => Self::FString,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Ref(_, s) => Some(s),
            Self::String(_, s) => Some(s),
            Self::FString => None,
        }
    }
}

fn parse_hex<'x, I: Iterator<Item = (usize, &'x u8)>>(count: usize, iterator: I) -> Option<char> {
    let mut number = 0;
    for (i, (_, x)) in iterator.take(count).enumerate() {
        let digit = if x.is_ascii_digit() {
            *x - b'0'
        } else if (b'a'..=b'f').contains(x) {
            *x - b'a' + 10
        } else if (b'A'..=b'F').contains(x) {
            *x - b'A' + 10
        } else {
            return None;
        };
        number += (digit as u32) << ((count - i - 1) * 4);
    }
    char::from_u32(number)
}

pub(crate) fn parse_python_octal(x: &[u8]) -> Option<(usize, char)> {
    // Parses "7" to 7 and "011" to 9
    let mut result = 0;
    let mut used_bytes = 0;
    for &b in x.iter().take(3) {
        let Some(x) = char::from_u32(b as u32).and_then(|c| c.to_digit(8)) else {
            break;
        };
        used_bytes += 1;
        result <<= 3;
        result += x;
    }
    (used_bytes > 0).then(|| (used_bytes, char::from_u32(result).unwrap()))
}

pub(crate) struct UnpackedLiteral<'x> {
    pub inner: &'x str,
    pub inner_start_offset: CodeIndex,
    pub had_raw_modifier: bool,
}

pub(crate) fn unpack_string_or_bytes_content(code: &str) -> UnpackedLiteral {
    let mut had_raw_modifier = false;
    let mut inner_start_offset = 0;
    let mut quote_len = 1;
    let mut byte_iterator = code.as_bytes().iter().enumerate();
    for (i, &b) in byte_iterator.by_ref() {
        match b {
            b'r' | b'R' => had_raw_modifier = true,
            b'\'' | b'"' => {
                if byte_iterator.len() > 3 {
                    let (_, &second) = byte_iterator.next().unwrap();
                    let (i, &third) = byte_iterator.next().unwrap();
                    if second == b && third == b {
                        quote_len = 3;
                        inner_start_offset = i + 1;
                        break;
                    }
                }
                inner_start_offset = i + 1;
                break;
            }
            _ => (), // All other modifiers don't matter
        }
    }
    UnpackedLiteral {
        inner: &code[inner_start_offset..code.len() - quote_len],
        inner_start_offset: inner_start_offset as CodeIndex,
        had_raw_modifier,
    }
}
