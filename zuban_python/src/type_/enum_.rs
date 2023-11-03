use std::{cell::OnceCell, rc::Rc};

use crate::{
    database::{Database, ParentScope, PointLink},
    inference_state::InferenceState,
    matching::FormatData,
    node_ref::NodeRef,
    type_helpers::Class,
};

use super::{DbString, FormatStyle, StringSlice};

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMember {
    pub enum_: Rc<Enum>,
    member_index: usize,
    pub(super) implicit: bool,
}

impl EnumMember {
    pub fn new(enum_: Rc<Enum>, member_index: usize, implicit: bool) -> Self {
        Self {
            enum_,
            member_index,
            implicit,
        }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.enum_.members[self.member_index].name(db)
    }

    pub fn value(&self) -> Option<PointLink> {
        self.enum_.members[self.member_index].value
    }

    pub fn is_same_member(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.enum_, &other.enum_) && self.member_index == other.member_index
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.enum_.format(format_data)
            }
            _ => "",
        };
        format!("Literal[{}]{question_mark}", self.format_inner(format_data))
    }

    pub fn format_inner(&self, format_data: &FormatData) -> String {
        format!(
            "{}.{}",
            &self.enum_.format(format_data),
            self.name(format_data.db)
        )
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct EnumMemberDefinition {
    name: DbString,
    pub value: Option<PointLink>,
}

impl EnumMemberDefinition {
    pub fn new(name: DbString, value: Option<PointLink>) -> Self {
        Self { name, value }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.name.as_str(db)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Enum {
    pub name: StringSlice,
    pub class: PointLink,
    defined_at: PointLink,
    parent_scope: ParentScope,
    pub members: Box<[EnumMemberDefinition]>,
    has_customized_new: OnceCell<bool>,
}

impl Enum {
    pub fn new(
        name: StringSlice,
        class: PointLink,
        defined_at: PointLink,
        parent_scope: ParentScope,
        members: Box<[EnumMemberDefinition]>,
        has_customized_new: OnceCell<bool>,
    ) -> Rc<Self> {
        Rc::new(Self {
            name,
            defined_at,
            parent_scope,
            class,
            members,
            has_customized_new,
        })
    }

    pub fn class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_link(db, self.class)
    }

    pub fn lookup(rc: &Rc<Enum>, db: &Database, name: &str, implicit: bool) -> Option<EnumMember> {
        for (index, member) in rc.members.iter().enumerate() {
            if name == member.name(db) {
                return Some(EnumMember::new(rc.clone(), index, implicit));
            }
        }
        None
    }

    pub fn has_customized_new(&self, i_s: &InferenceState) -> bool {
        *self
            .has_customized_new
            .get_or_init(|| self.class(i_s.db).has_customized_enum_new(i_s))
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let enum_name = self.name.as_str(format_data.db);
        match format_data.style {
            FormatStyle::Short if !format_data.verbose => enum_name.to_string(),
            _ => self.parent_scope.qualified_name(
                format_data.db,
                NodeRef::from_link(format_data.db, self.defined_at),
                enum_name,
            ),
        }
    }
}
