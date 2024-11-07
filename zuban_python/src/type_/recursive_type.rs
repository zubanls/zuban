use std::{
    cell::OnceCell,
    hash::{Hash, Hasher},
};

use super::{ClassGenerics, Dataclass, GenericClass, GenericsList, Type};
use crate::{
    database::{Database, PointLink, TypeAlias},
    matching::Generics,
    node_ref::NodeRef,
    type_helpers::Class,
};

#[derive(Clone, Eq)]
pub struct RecursiveType {
    pub link: PointLink,
    pub generics: Option<GenericsList>,
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
        match self.origin(db) {
            RecursiveTypeOrigin::TypeAlias(alias) => alias.name(db).unwrap(),
            RecursiveTypeOrigin::Class(class) => class.name(),
        }
    }

    pub fn origin<'x>(&'x self, db: &'x Database) -> RecursiveTypeOrigin<'x> {
        let from = NodeRef::from_link(db, self.link);
        match from.maybe_alias() {
            Some(alias) => RecursiveTypeOrigin::TypeAlias(alias),
            None => RecursiveTypeOrigin::Class(Class::from_position(
                from,
                match &self.generics {
                    Some(list) => Generics::List(list, None),
                    None => Generics::None,
                },
                None,
            )),
        }
    }

    pub fn has_alias_origin(&self, db: &Database) -> bool {
        NodeRef::from_link(db, self.link).maybe_alias().is_some()
    }

    pub fn calculating(&self, db: &Database) -> bool {
        match self.origin(db) {
            RecursiveTypeOrigin::TypeAlias(alias) => alias.calculating(),
            RecursiveTypeOrigin::Class(class) => class.is_calculating_class_infos(),
        }
    }

    pub fn calculated_type<'db: 'slf, 'slf>(&'slf self, db: &'db Database) -> &'slf Type {
        let alias = self.origin(db);
        match self.origin(db) {
            RecursiveTypeOrigin::TypeAlias(alias) => {
                if self.generics.is_none() {
                    alias.type_if_valid()
                } else {
                    self.calculated_type.get_or_init(|| {
                        alias
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
            RecursiveTypeOrigin::Class(class) => self.calculated_type.get_or_init(|| {
                let class_generics = if let Some(generics) = &self.generics {
                    ClassGenerics::List(generics.clone())
                } else {
                    ClassGenerics::None
                };
                if let Some(dataclass) = class.maybe_dataclass(db) {
                    Type::Dataclass(Dataclass::new(
                        GenericClass {
                            link: self.link,
                            generics: class_generics,
                        },
                        dataclass.options,
                    ))
                } else if let Some(td) = class.maybe_typed_dict() {
                    Type::TypedDict(match self.generics.clone() {
                        Some(list) => td.apply_generics(db, list),
                        None => td,
                    })
                } else {
                    Type::new_class(self.link, class_generics)
                }
            }),
        }
    }
}

impl std::cmp::PartialEq for RecursiveType {
    fn eq(&self, other: &Self) -> bool {
        self.link == other.link && self.generics == other.generics
    }
}

impl Hash for RecursiveType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.link.hash(state);
        self.generics.hash(state);
    }
}

impl std::fmt::Debug for RecursiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct(stringify!(RecursiveType))
            .field("link", &self.link)
            .field("generics", &self.generics)
            .finish()
    }
}

pub enum RecursiveTypeOrigin<'x> {
    TypeAlias(&'x TypeAlias),
    Class(Class<'x>),
}
