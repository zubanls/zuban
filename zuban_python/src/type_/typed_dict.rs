use std::rc::Rc;

use crate::{
    database::{Database, PointLink},
    inference_state::InferenceState,
    matching::FormatData,
    type_helpers::Module,
    utils::join_with_commas,
};

use super::{FormatStyle, GenericsList, RecursiveAlias, StringSlice, Type, TypeVarLikes};

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDictMember {
    pub name: StringSlice,
    pub type_: Type,
    pub required: bool,
}

impl TypedDictMember {
    pub fn replace_type(&self, callable: impl FnOnce(&Type) -> Type) -> Self {
        Self {
            name: self.name,
            type_: callable(&self.type_),
            required: self.required,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedDictGenerics {
    None,
    NotDefinedYet(TypeVarLikes),
    Generics(GenericsList),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedDict {
    pub name: Option<StringSlice>,
    pub members: Box<[TypedDictMember]>,
    pub defined_at: PointLink,
    pub generics: TypedDictGenerics,
}

impl TypedDict {
    pub fn new(
        name: Option<StringSlice>,
        members: Box<[TypedDictMember]>,
        defined_at: PointLink,
        generics: TypedDictGenerics,
    ) -> Rc<Self> {
        Rc::new(Self {
            name,
            members,
            defined_at,
            generics,
        })
    }

    pub fn new_definition(
        name: StringSlice,
        members: Box<[TypedDictMember]>,
        defined_at: PointLink,
        type_var_likes: TypeVarLikes,
    ) -> Rc<Self> {
        let generics = if type_var_likes.is_empty() {
            TypedDictGenerics::None
        } else {
            TypedDictGenerics::NotDefinedYet(type_var_likes)
        };
        Rc::new(Self {
            name: Some(name),
            members,
            defined_at,
            generics,
        })
    }

    pub fn replace_type_var_likes(&self, db: &Database, generics: GenericsList) -> Rc<Self> {
        let members = self
            .members
            .iter()
            .map(|m| {
                m.replace_type(|t| {
                    m.type_
                        .replace_type_var_likes(db, &mut |usage| generics[usage.index()].clone())
                })
            })
            .collect::<Box<[_]>>();
        TypedDict::new(
            self.name,
            members,
            self.defined_at,
            TypedDictGenerics::Generics(generics),
        )
    }

    pub fn find_member(&self, db: &Database, name: &str) -> Option<&TypedDictMember> {
        self.members.iter().find(|p| p.name.as_str(db) == name)
    }

    fn qualified_name(&self, db: &Database) -> Option<String> {
        let Some(name) = self.name else {
            return None
        };
        let module = Module::from_file_index(db, name.file_index).qualified_name(db);
        Some(format!("{module}.{}", name.as_str(db)))
    }

    pub fn union(&self, i_s: &InferenceState, other: &Self) -> Type {
        let mut members = self.members.clone().into_vec();
        'outer: for m2 in other.members.iter() {
            for m1 in members.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db) {
                    if m1.required != m2.required
                        || !m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                    {
                        return Type::Never;
                    }
                    continue 'outer;
                }
            }
            members.push(m2.clone());
        }
        Type::TypedDict(Self::new(
            None,
            members.into_boxed_slice(),
            self.defined_at,
            TypedDictGenerics::None,
        ))
    }

    pub fn intersection(&self, i_s: &InferenceState, other: &Self) -> Rc<TypedDict> {
        let mut new_members = vec![];
        for m1 in self.members.iter() {
            for m2 in other.members.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db) {
                    if m1.required == m2.required
                        && m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                    {
                        new_members.push(m1.clone());
                    }
                }
            }
        }
        Self::new(
            None,
            new_members.into_boxed_slice(),
            self.defined_at,
            TypedDictGenerics::None,
        )
    }

    pub fn name_or_fallback(&self, format_data: &FormatData) -> String {
        if let Some(name) = self.name {
            name.as_str(format_data.db).into()
        } else {
            self.format_full(format_data, None)
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        match format_data.style {
            FormatStyle::MypyRevealType => {
                self.format_full(format_data, self.qualified_name(format_data.db).as_deref())
            }
            FormatStyle::Short if !format_data.verbose => self.name_or_fallback(format_data),
            _ => self
                .qualified_name(format_data.db)
                .unwrap_or_else(|| todo!()),
        }
    }

    pub fn format_full(&self, format_data: &FormatData, name: Option<&str>) -> String {
        let rec = RecursiveAlias::new(self.defined_at, None);
        if format_data.has_already_seen_recursive_alias(&rec) {
            return "...".to_string();
        }
        let format_data = &format_data.with_seen_recursive_alias(&rec);
        let params = join_with_commas(self.members.iter().map(|p| {
            format!(
                "'{}'{}: {}",
                p.name.as_str(format_data.db),
                match p.required {
                    true => "",
                    false => "?",
                },
                p.type_.format(format_data)
            )
        }));
        if let Some(name) = name {
            format!("TypedDict('{name}', {{{params}}})").into()
        } else {
            format!("TypedDict({{{params}}})").into()
        }
    }
}
