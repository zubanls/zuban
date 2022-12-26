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
    pub fn new(strings: SiblingIterator<'db>) -> Option<Self> {
        let mut result: Option<Self> = None;
        for literal in strings {
            result = Some(match result {
                Some(s) => s.union(Self::from_literal(literal)),
                None => Self::from_literal(literal),
            });
        }
        result
    }

    fn from_literal(literal: PyNode<'db>) -> Self {
        if literal.is_type(Nonterminal(fstring)) {
            Self::FString
        } else {
            let code = literal.as_code();
            if !code.starts_with(['"', '\''].as_slice()) {
                todo!()
            }
            let inner = &code[1..code.len() - 1];

            let quote = code.as_bytes()[0];
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
                    match ch {
                        b'\\' => todo!(),
                        _ if *ch == quote => s.push(quote as char),
                        _ => todo!(),
                    }
                }
            }
            if let Some(mut string) = string {
                string.push_str(&inner[previous_insert..inner.len()]);
                Self::String(literal.start() + 1, string)
            } else {
                Self::Ref(literal.start() + 1, inner)
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
