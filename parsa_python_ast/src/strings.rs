use std::borrow::Cow;

use parsa_python::NonterminalType::fstring;
use parsa_python::PyNodeType::Nonterminal;
use parsa_python::{CodeIndex, PyNode, SiblingIterator};

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

    pub fn into_cow(self) -> Option<Cow<'db, str>> {
        match self {
            Self::Ref(_, s) => Some(Cow::Borrowed(s)),
            Self::String(_, s) => Some(Cow::Owned(s)),
            Self::FString => None,
        }
    }

    pub fn from_literal(literal: PyNode<'db>) -> Self {
        if literal.is_type(Nonterminal(fstring)) {
            Self::FString
        } else {
            let code = literal.as_code();
            let bytes = code.as_bytes();
            let mut quote = bytes[0];
            let start = match quote {
                b'u' | b'U' => {
                    quote = bytes[0];
                    2
                }
                b'r' | b'R' => {
                    quote = bytes[0];
                    2
                }
                _ => {
                    debug_assert!(quote == b'"' || quote == b'\'');
                    1
                }
            };
            let inner = &code[start..code.len() - 1];

            let mut iterator = inner.as_bytes().iter().enumerate().peekable();
            let mut string = None;
            let mut previous_insert = 0;
            while let Some((i, mut ch)) = iterator.next() {
                if ch == &b'\\' {
                    if string.is_none() {
                        string = Some(String::with_capacity(inner.len()));
                    }
                    let s = string.as_mut().unwrap();
                    s.push_str(&inner[previous_insert..i]);
                    (_, ch) = iterator.next().unwrap();

                    s.push(match ch {
                        b'\\' | b'\'' | b'"' => quote as char,
                        b'\n' => todo!(),
                        b'u' => parse_hex(4, iterator.by_ref()),
                        b'U' => parse_hex(8, iterator.by_ref()),
                        b'x' => parse_hex(2, iterator.by_ref()),
                        b'N' => todo!(),
                        b'a' => todo!(),
                        b'b' => todo!(),
                        b'f' => todo!(),
                        b'n' => '\n',
                        b'r' => todo!(),
                        b't' => todo!(),
                        b'v' => todo!(),
                        // TODO also \ooo (where o is 0-7) (octal)
                        _ => todo!("{inner:?}"),
                    });
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
            Self::Ref(start, s1) => match self {
                Self::Ref(_, s2) => Self::String(start, s1.to_owned() + s2),
                Self::String(_, s2) => Self::String(start, s1.to_owned() + &s2),
                Self::FString => todo!(),
            },
            Self::String(start, s1) => match self {
                Self::Ref(_, s2) => Self::String(start, s1 + s2),
                Self::String(_, s2) => Self::String(start, s1 + &s2),
                Self::FString => todo!(),
            },
            Self::FString => Self::FString,
        }
    }
}

fn parse_hex<'x, I: Iterator<Item = (usize, &'x u8)>>(count: usize, iterator: I) -> char {
    let mut number = 0;
    for (i, (_, x)) in iterator.take(count).enumerate() {
        let digit = if (b'0'..=b'9').contains(x) {
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
