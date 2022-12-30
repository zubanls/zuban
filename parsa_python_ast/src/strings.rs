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

            let mut iterator = inner.as_bytes().iter().enumerate();
            let mut string = None;
            let mut previous_insert = 0;
            while let Some((i, mut ch)) = iterator.next() {
                if ch == &b'\\' {
                    if string.is_none() {
                        string = Some(String::with_capacity(inner.len()));
                    }
                    let s = string.as_mut().unwrap();
                    s.push_str(&inner[previous_insert..i]);
                    (previous_insert, ch) = iterator.next().unwrap();
                    previous_insert += 1;
                    match ch {
                        b'\\' => todo!(),
                        _ if *ch == quote => s.push(quote as char),
                        _ => todo!(),
                    }
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
