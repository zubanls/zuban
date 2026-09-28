use std::hash::{Hash, Hasher};

use crate::{
    database::{Database, PointLink},
    format_data::FormatData,
    node_ref::NodeRef,
    type_::{FormatStyle, Type},
};

#[derive(Debug, Clone, Eq)]
pub(crate) struct NewType {
    pub name_node: PointLink,
    pub name_string: PointLink,
    pub type_: Type,
}

impl NewType {
    pub fn new(name_node: PointLink, name_string: PointLink, type_: Type) -> Self {
        Self {
            name_node,
            name_string,
            type_,
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match format_data.style {
            FormatStyle::Short if !format_data.should_format_qualified(self.name_string) => {
                self.name(format_data.db).into()
            }
            _ => self.qualified_name(format_data.db),
        }
    }

    pub fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name_string)
            .maybe_str()
            .unwrap()
            .content()
    }

    pub fn qualified_name(&self, db: &Database) -> Box<str> {
        let node_ref = NodeRef::from_link(db, self.name_string);
        format!(
            "{}.{}",
            node_ref.file.qualified_name(db),
            node_ref.maybe_str().unwrap().content()
        )
        .into()
    }
}

impl PartialEq for NewType {
    fn eq(&self, other: &Self) -> bool {
        self.name_string == other.name_string
    }
}

impl Hash for NewType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name_string.hash(state);
    }
}
