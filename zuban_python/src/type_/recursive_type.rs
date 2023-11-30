use std::cell::OnceCell;

use crate::{
    database::{Database, PointLink, TypeAlias},
    node_ref::NodeRef,
};

use super::{GenericsList, Type};

#[derive(Debug, Clone)]
pub struct RecursiveType {
    pub(super) link: PointLink,
    pub(super) generics: Option<GenericsList>,
    calculated_type: OnceCell<Type>,
}

impl RecursiveType {
    pub fn new(link: PointLink, generics: Option<GenericsList>) -> Self {
        Self {
            link,
            generics,
            calculated_type: OnceCell::new(),
        }
    }

    pub(super) fn name<'x>(&'x self, db: &'x Database) -> &str {
        let alias = self.type_alias(db);
        alias.name(db).unwrap()
    }

    pub(super) fn type_alias<'db>(&self, db: &'db Database) -> &'db TypeAlias {
        NodeRef::from_link(db, self.link).maybe_alias().unwrap()
    }

    pub(super) fn calculated_type<'db: 'slf, 'slf>(&'slf self, db: &'db Database) -> &'slf Type {
        let alias = self.type_alias(db);
        if self.generics.is_none() {
            alias.type_if_valid()
        } else {
            self.calculated_type.get_or_init(|| {
                self.type_alias(db)
                    .replace_type_var_likes(db, true, &mut |t| {
                        self.generics
                            .as_ref()
                            .map(|g| g.nth(t.index()).unwrap().clone())
                            .unwrap()
                    })
                    .into_owned()
            })
        }
    }
}

impl std::cmp::PartialEq for RecursiveType {
    fn eq(&self, other: &Self) -> bool {
        self.link == other.link && self.generics == other.generics
    }
}
