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
            let c = &code[1..code.len() - 1];
            if c.contains(['\'', '\\', '"'].as_slice()) {
                todo!()
            }
            Self::Ref(literal.start() + 1, c)
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
