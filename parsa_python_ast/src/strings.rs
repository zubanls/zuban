use parsa_python::NonterminalType::fstring;
use parsa_python::PyNodeType::Nonterminal;
use parsa_python::{PyNode, SiblingIterator};

#[derive(Debug)]
pub enum PythonString<'db> {
    Ref(&'db str),
    String(String),
    FString,
}

impl<'db> PythonString<'db> {
    pub fn new(strings: SiblingIterator<'db>) -> Option<Self> {
        let mut result: Option<Self> = None;
        for literal in strings {
            if !starts_with_string(&literal) {
                return None;
            }
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
            let c = &code[1..code.len() - 1];
            if c.contains(['\'', '\\', '"'].as_slice()) {
                todo!()
            }
            Self::Ref(c)
        }
    }

    fn union(self, other: Self) -> Self {
        match other {
            Self::Ref(s2) => match self {
                Self::Ref(s1) => Self::String(s1.to_owned() + s2),
                Self::String(s1) => Self::String(s1 + s2),
                Self::FString => unreachable!(),
            },
            Self::String(s2) => match self {
                Self::Ref(s1) => Self::String(s1.to_owned() + &s2),
                Self::String(s1) => Self::String(s1 + &s2),
                Self::FString => unreachable!(),
            },
            Self::FString => Self::FString,
        }
    }

    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Ref(s) => Some(s),
            Self::String(s) => Some(s),
            Self::FString => None,
        }
    }
}

pub fn starts_with_string(literal: &PyNode) -> bool {
    let code = literal.as_code();
    for byte in code.bytes() {
        if byte == b'"' || byte == b'\'' {
            break;
        } else if byte == b'b' || byte == b'B' {
            return false;
        }
    }
    true
}
