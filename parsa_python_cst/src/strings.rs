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
            let bytes = code.as_bytes();
            let quote = bytes[0];
            let start = match quote {
                b'u' | b'U' => 2,
                b'r' | b'R' => return Self::Ref(literal.start() + 2, &code[2..code.len() - 1]),
                _ => {
                    debug_assert!(quote == b'"' || quote == b'\'');
                    1
                }
            };
            let inner = &code[start..code.len() - 1];

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
                        b'u' => s.push(parse_hex(4, iterator.by_ref())),
                        b'U' => s.push(parse_hex(8, iterator.by_ref())),
                        b'x' => s.push(parse_hex(2, iterator.by_ref())),
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
                            if let Some((len, octal)) = parse_python_octal(string_from_here) {
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
                Self::String(literal.start() + start as u32, string)
            } else {
                Self::Ref(literal.start() + start as u32, inner)
            }
        }
    }

    fn union(self, other: Self) -> Self {
        match other {
            Self::Ref(start, s2) => match self {
                Self::Ref(_, s1) => Self::String(start, s1.to_owned() + s2),
                Self::String(_, s1) => Self::String(start, s1 + s2),
                Self::FString => todo!(),
            },
            Self::String(start, s2) => match self {
                Self::Ref(_, s1) => Self::String(start, s1.to_owned() + &s2),
                Self::String(_, s1) => Self::String(start, s1 + &s2),
                Self::FString => todo!(),
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

fn parse_hex<'x, I: Iterator<Item = (usize, &'x u8)>>(count: usize, iterator: I) -> char {
    let mut number = 0;
    for (i, (_, x)) in iterator.take(count).enumerate() {
        let digit = if x.is_ascii_digit() {
            *x - b'0'
        } else if (b'a'..=b'f').contains(x) {
            *x - b'a' + 10
        } else if (b'A'..=b'F').contains(x) {
            *x - b'A' + 10
        } else {
            todo!()
        };
        number += (digit as u32) << ((count - i - 1) * 4);
    }
    char::from_u32(number).unwrap_or_else(|| todo!())
}

fn parse_python_octal(x: &str) -> Option<(usize, char)> {
    // Parses "7" to 7 and "011" to 9
    let x = x;
    let len = x
        .chars()
        .take(3)
        .take_while(|c| c.to_digit(8).is_some())
        .count();
    let c = u32::from_str_radix(&x[..len], 8).ok()?;
    char::from_u32(c).map(|c| (len, c))
}
