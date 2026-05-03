use crate::{
    database::{Database, PointLink},
    format_data::FormatData,
    node_ref::NodeRef,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Sentinel {
    name: PointLink,
}

impl Sentinel {
    pub(crate) fn new(name: PointLink) -> Self {
        Self { name }
    }

    fn name<'db>(&self, db: &'db Database) -> &'db str {
        NodeRef::from_link(db, self.name)
            .maybe_str()
            .unwrap()
            .content()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        format!("Sentinel('{}')", self.name(format_data.db)).into()
    }
}
