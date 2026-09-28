use std::{borrow::Cow, hash::Hasher, sync::Arc};

use parsa_python_cst::{CodeIndex, Expression, Name, PythonString};
use vfs::FileIndex;

use crate::{
    database::{Database, PointLink},
    file::ClassNodeRef,
    format_data::FormatData,
    node_ref::NodeRef,
    type_::{ClassGenerics, Type},
    type_helpers::{Class, Instance},
    utils::{bytes_repr, str_repr},
};

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub(crate) enum FormatStyle {
    Short,
    MypyRevealType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StringSlice {
    pub file_index: FileIndex,
    pub start: CodeIndex,
    pub end: CodeIndex,
}

impl StringSlice {
    pub fn from_string_in_expression(file_index: FileIndex, expr: Expression) -> Option<Self> {
        if let Some(literal) = expr.maybe_single_string_literal() {
            let (start, end) = literal.content_start_and_end_in_literal();
            let s = literal.start();
            Some(Self::new(file_index, s + start, s + end))
        } else {
            None
        }
    }

    pub fn from_name(file_index: FileIndex, name: Name) -> Self {
        Self::new(file_index, name.start(), name.end())
    }

    pub fn new(file_index: FileIndex, start: CodeIndex, end: u32) -> Self {
        Self {
            file_index,
            start,
            end,
        }
    }

    pub fn as_str(self, db: &Database) -> &str {
        let file = db.loaded_python_file(self.file_index);
        &file.tree.code()[self.start as usize..self.end as usize]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DbString {
    StringSlice(StringSlice),
    ArcStr(Arc<str>),
    Static(&'static str),
}

impl DbString {
    pub fn as_str<'x>(&'x self, db: &'x Database) -> &'x str {
        match self {
            Self::StringSlice(s) => s.as_str(db),
            Self::ArcStr(s) => s,
            Self::Static(s) => s,
        }
    }

    pub fn from_python_string(file_index: FileIndex, python_string: PythonString) -> Option<Self> {
        match python_string {
            PythonString::Ref(code_index, s) => Some(Self::StringSlice(StringSlice::new(
                file_index,
                code_index,
                code_index + s.len() as CodeIndex,
            ))),
            PythonString::String(_, s) => Some(Self::ArcStr(s.into())),
            PythonString::FString => None,
        }
    }
}

impl From<StringSlice> for DbString {
    fn from(item: StringSlice) -> Self {
        Self::StringSlice(item)
    }
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct Literal {
    pub kind: LiteralKind,
    pub implicit: bool,
}

impl std::cmp::PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl std::hash::Hash for Literal {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LiteralKind {
    String(DbString),
    Int(num_bigint::BigInt),
    Bytes(DbBytes),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DbBytes {
    Link(PointLink),
    Static(&'static [u8]),
    Arc(Arc<[u8]>),
}

#[derive(PartialEq, Eq, Debug, Hash)]
pub(crate) enum LiteralValue<'db> {
    String(&'db str),
    Int(&'db num_bigint::BigInt),
    Bytes(Cow<'db, [u8]>),
    Bool(bool),
}

impl Literal {
    pub fn new(kind: LiteralKind) -> Self {
        Self {
            kind,
            implicit: false,
        }
    }

    pub fn new_implicit(kind: LiteralKind) -> Self {
        Self {
            kind,
            implicit: true,
        }
    }

    pub fn value<'x>(&'x self, db: &'x Database) -> LiteralValue<'x> {
        match &self.kind {
            LiteralKind::Int(i) => LiteralValue::Int(i),
            LiteralKind::String(s) => LiteralValue::String(s.as_str(db)),
            LiteralKind::Bool(b) => LiteralValue::Bool(*b),
            LiteralKind::Bytes(b) => match b {
                DbBytes::Link(link) => {
                    let node_ref = NodeRef::from_link(db, *link);
                    LiteralValue::Bytes(node_ref.expect_bytes_literal().content_as_bytes())
                }
                DbBytes::Static(b) => LiteralValue::Bytes(Cow::Borrowed(b)),
                DbBytes::Arc(b) => LiteralValue::Bytes(Cow::Borrowed(b)),
            },
        }
    }

    pub(super) fn format_inner(&self, db: &Database) -> Cow<'_, str> {
        match self.value(db) {
            LiteralValue::String(s) => Cow::Owned(str_repr(s)),
            LiteralValue::Int(i) => Cow::Owned(format!("{i}")),
            LiteralValue::Bool(true) => Cow::Borrowed("True"),
            LiteralValue::Bool(false) => Cow::Borrowed("False"),
            LiteralValue::Bytes(b) => Cow::Owned(bytes_repr(b)),
        }
    }

    pub fn fallback_node_ref<'db>(&self, db: &'db Database) -> ClassNodeRef<'db> {
        match &self.kind {
            LiteralKind::Int(_) => db.python_state.int_node_ref(),
            LiteralKind::String(_) => db.python_state.str_node_ref(),
            LiteralKind::Bool(_) => db.python_state.bool_node_ref(),
            LiteralKind::Bytes(_) => db.python_state.bytes_node_ref(),
        }
    }

    pub fn fallback_class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_node_ref(self.fallback_node_ref(db))
    }

    pub fn as_instance<'db>(&self, db: &'db Database) -> Instance<'db> {
        Instance::new(
            Class::from_non_generic_node_ref(self.fallback_node_ref(db)),
            None,
        )
    }

    pub fn fallback_type(&self, db: &Database) -> Type {
        Type::new_class(
            self.fallback_node_ref(db).as_link(),
            ClassGenerics::new_none(),
        )
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.fallback_type(format_data.db).format(format_data);
            }
            _ => "",
        };
        format!(
            "Literal[{}]{}",
            self.format_inner(format_data.db),
            question_mark
        )
        .into()
    }
}
