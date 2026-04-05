use std::{
    hash::{Hash, Hasher},
    sync::{Arc, OnceLock},
};

use super::{
    AnyCause, CallableLike, DbString, FormatStyle, Literal, LiteralKind, LookupResult, Type,
};
use crate::{
    database::{ComplexPoint, Database, ParentScope, PointLink},
    debug,
    diagnostics::IssueKind,
    file::File as _,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::LookupKind,
    node_ref::NodeRef,
    type_helpers::{
        Class, ClassLookupOptions, Instance, InstanceLookupOptions, LookupDetails, TypeOrClass,
    },
};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub(crate) struct EnumMember {
    pub enum_: Arc<Enum>,
    pub member_index: usize,
    pub implicit: bool,
}

impl EnumMember {
    pub fn new(enum_: Arc<Enum>, member_index: usize, implicit: bool) -> Self {
        Self {
            enum_,
            member_index,
            implicit,
        }
    }

    pub fn name<'x>(&'x self, db: &'x Database) -> &'x str {
        self.member_definition().name(db)
    }

    pub fn name_node<'db>(&self, db: &'db Database) -> Option<NodeRef<'db>> {
        let n = NodeRef::from_link(db, self.member_definition().value?);
        // On classes the enum members are defined on names
        n.maybe_name().map(|_| n)
    }

    pub fn value(&self) -> Option<PointLink> {
        self.member_definition().value
    }

    pub fn infer_value(&self, i_s: &InferenceState) -> Inferred {
        self.member_definition().infer_value(i_s, &self.enum_)
    }

    pub fn is_same_member(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.enum_, &other.enum_) && self.member_index == other.member_index
    }

    fn member_definition(&self) -> &EnumMemberDefinition {
        &self.enum_.members[self.member_index]
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        let question_mark = match format_data.style {
            FormatStyle::MypyRevealType if self.implicit => "?",
            _ if self.implicit && format_data.hide_implicit_literals => {
                return self.enum_.format(format_data);
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct EnumMemberDefinition {
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

    pub fn infer_value(&self, i_s: &InferenceState, enum_: &Enum) -> Inferred {
        match self.value {
            // I'm not 100% sure why this is, but Mypy returns Any on all enums that have a __new__
            // defined.
            Some(link) if !enum_.has_customized_new(i_s) => {
                let node_ref = NodeRef::from_link(i_s.db, link);
                let enum_class = enum_.class(i_s.db);
                let class_i_s = &i_s.with_class_context(&enum_class);
                let inferred = if let Some(name) = node_ref.maybe_name() {
                    node_ref
                        .file
                        .inference(&class_i_s.with_enum_calculation_mode())
                        .infer_name_of_definition(name)
                } else {
                    let expr = node_ref.expect_expression();
                    node_ref.file.inference(class_i_s).infer_expression(expr)
                };
                match inferred.as_cow_type(class_i_s).as_ref() {
                    Type::Class(c) if c.link == i_s.db.python_state.enum_auto_link() => {
                        let result = if enum_.kind(i_s) == EnumKind::StrEnum {
                            Type::Literal(Literal::new_implicit(LiteralKind::String(
                                DbString::ArcStr(self.name(i_s.db).to_lowercase().into()),
                            )))
                        } else {
                            enum_class
                                .simple_lookup(
                                    i_s,
                                    |issue| node_ref.add_issue(i_s, issue),
                                    "_generate_next_value_",
                                )
                                .into_maybe_inferred()
                                .and_then(|inf| {
                                    // Check We have a proper callable that is not part of the enum module
                                    // and overwrites the default of int.
                                    if inf.maybe_saved_link().is_some_and(|link| {
                                        link.file == i_s.db.python_state.enum_file().file_index
                                    }) {
                                        return None;
                                    }
                                    inf.as_cow_type(i_s).maybe_callable(i_s)
                                })
                                .map(|callable| match callable {
                                    CallableLike::Callable(c) => c.return_type.clone(),
                                    CallableLike::Overload(_) => {
                                        debug!("TODO overloads are currently not supported for _generate_next_value_");
                                        Type::Any(AnyCause::Internal)
                                    }
                                })
                                .unwrap_or(i_s.db.python_state.int_type())
                        };
                        Inferred::from_type(result)
                    }
                    _ => inferred,
                }
            }
            _ => Inferred::new_any(AnyCause::Todo),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct EnumMemberAlias {
    name: DbString,
    pointing_to_name: DbString,
}

impl EnumMemberAlias {
    pub fn new(name: DbString, pointing_to_name: DbString) -> Self {
        Self {
            name,
            pointing_to_name,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Enum {
    pub name: DbString,
    pub class: PointLink,
    pub defined_at: PointLink,
    parent_scope: ParentScope,
    pub members: Box<[EnumMemberDefinition]>,
    pub member_aliases: Box<[EnumMemberAlias]>,
    has_customized_new: OnceLock<bool>,
}

impl Enum {
    pub fn new(
        name: DbString,
        class: PointLink,
        defined_at: PointLink,
        parent_scope: ParentScope,
        members: Box<[EnumMemberDefinition]>,
        member_aliases: Box<[EnumMemberAlias]>,
        has_customized_new: OnceLock<bool>,
    ) -> Arc<Self> {
        Arc::new(Self {
            name,
            defined_at,
            parent_scope,
            class,
            members,
            has_customized_new,
            member_aliases,
        })
    }

    pub fn class<'db>(&self, db: &'db Database) -> Class<'db> {
        Class::from_non_generic_link(db, self.class)
    }

    pub fn implicit_members(rc: &Arc<Enum>) -> impl Iterator<Item = EnumMember> {
        rc.members
            .iter()
            .enumerate()
            .map(|(i, _)| EnumMember::new(rc.clone(), i, false))
    }

    pub fn lookup(rc: &Arc<Enum>, db: &Database, name: &str, implicit: bool) -> Option<EnumMember> {
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
            FormatStyle::Short if !format_data.should_format_qualified(self.defined_at) => {
                enum_name.to_string()
            }
            _ => self.parent_scope.qualified_name(
                format_data.db,
                NodeRef::from_link(format_data.db, self.defined_at),
                enum_name,
            ),
        }
    }

    pub(crate) fn kind(&self, i_s: &InferenceState) -> EnumKind {
        let class = self.class(i_s.db);
        for (_, in_mro) in class.mro(i_s.db) {
            let TypeOrClass::Class(in_mro) = in_mro else {
                continue;
            };
            if in_mro.node_ref.file_index() == i_s.db.python_state.enum_file().file_index() {
                let name = in_mro.name();
                if name == "IntEnum" {
                    return EnumKind::IntEnum;
                } else if name == "StrEnum" {
                    return EnumKind::StrEnum;
                }
            }
        }
        EnumKind::Normal
    }

    pub fn is_from_functional_definition(&self, db: &Database) -> bool {
        self.class.file == db.python_state.enum_file().file_index()
    }

    pub fn has_customized_dunder_init(&self, i_s: &InferenceState) -> bool {
        let lookup = self.class(i_s.db).instance().lookup_on_self(
            i_s,
            &|_issue| false,
            "__init__",
            LookupKind::Normal,
        );
        lookup.lookup.is_some()
            && match lookup.class {
                TypeOrClass::Type(_) => true,
                TypeOrClass::Class(class) => {
                    class.file.file_index != i_s.db.python_state.builtins().file_index
                }
            }
    }
}

impl PartialEq for Enum {
    fn eq(&self, other: &Self) -> bool {
        self.defined_at == other.defined_at
    }
}

impl Eq for Enum {}

impl Hash for Enum {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.defined_at.hash(state);
    }
}

#[derive(PartialEq)]
pub(crate) enum EnumKind {
    Normal,
    IntEnum,
    StrEnum,
}

pub(crate) fn lookup_on_enum_class<'a>(
    i_s: &InferenceState<'a, '_>,
    add_issue: impl Fn(IssueKind) -> bool,
    in_type: &Arc<Type>,
    enum_: &Arc<Enum>,
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    match name {
        "_ignore_" | "_order_" | "__order__" => LookupDetails::none(),
        _ => LookupDetails::new(
            Type::Enum(enum_.clone()),
            lookup_members_or_aliases_on_enum(i_s, enum_, name),
            AttributeKind::Attribute,
        )
        .or_else(|| {
            enum_
                .class(i_s.db)
                .lookup(
                    i_s,
                    name,
                    ClassLookupOptions::new(&add_issue)
                        .with_kind(kind)
                        .with_as_type_type(&|| Type::Type(in_type.clone())),
                )
                .remove_non_member_from_enum(i_s.db)
        }),
    }
}

impl LookupDetails<'_> {
    fn remove_non_member_from_enum(mut self, db: &Database) -> Self {
        if let Some(inf) = self.lookup.maybe_inferred()
            && let Some(ComplexPoint::TypeInstance(Type::Class(c))) = inf.maybe_complex_point(db)
            && Some(c.link) == db.python_state.enum_nonmember_link()
        {
            let first_generic = c.class(db).nth_type_argument(db, 0);
            self.lookup
                .update_inferred(Inferred::from_type(first_generic.clone()))
        }
        self
    }
}

pub(crate) fn lookup_on_enum_instance<'a>(
    i_s: &'a InferenceState,
    add_issue: &dyn Fn(IssueKind) -> bool,
    enum_: &'a Arc<Enum>,
    name: &str,
) -> LookupDetails<'a> {
    match name {
        "value" | "_value_" => LookupDetails::new(
            Type::Enum(enum_.clone()),
            LookupResult::UnknownName(Inferred::gather_simplified_union(i_s, |add| {
                for member in enum_.members.iter() {
                    add(member.infer_value(i_s, enum_))
                }
            })),
            AttributeKind::Attribute,
        ),
        "_ignore_" => LookupDetails::none(),
        _ => lookup_on_enum_instance_fallback(i_s, add_issue, enum_, name),
    }
}

fn lookup_on_enum_instance_fallback<'a>(
    i_s: &'a InferenceState,
    add_issue: &dyn Fn(IssueKind) -> bool,
    enum_: &'a Arc<Enum>,
    name: &str,
) -> LookupDetails<'a> {
    let lookup = lookup_members_or_aliases_on_enum(i_s, enum_, name);
    if lookup.is_some() {
        LookupDetails::new(Type::Enum(enum_.clone()), lookup, AttributeKind::Attribute)
    } else {
        Instance::new(enum_.class(i_s.db), None)
            .lookup(
                i_s,
                name,
                InstanceLookupOptions::new(add_issue)
                    .with_as_self_instance(&|| Type::Enum(enum_.clone())),
            )
            .remove_non_member_from_enum(i_s.db)
    }
}

pub(crate) fn lookup_on_enum_member_instance<'a>(
    i_s: &'a InferenceState,
    add_issue: &dyn Fn(IssueKind) -> bool,
    member: &'a EnumMember,
    name: &str,
) -> LookupDetails<'a> {
    let enum_class = member.enum_.class(i_s.db);
    enum_class.use_cached_class_infos(i_s.db);
    let is_enum = enum_class.mro(i_s.db).any(|(_, base)| match base {
        TypeOrClass::Class(c) => c.node_ref == i_s.db.python_state.enum_node_ref(),
        _ => false,
    });
    // An enum cannot be an Enum, but just an instance of the EnumType metaclass. In that case
    // these specific hardcoded cases don't apply anymore.
    if is_enum {
        match name {
            "name" | "_name_" => {
                return LookupDetails::new(
                    Type::Enum(member.enum_.clone()),
                    LookupResult::UnknownName(Inferred::from_type(Type::Literal(Literal {
                        implicit: true,
                        kind: LiteralKind::String(DbString::ArcStr(member.name(i_s.db).into())),
                    }))),
                    AttributeKind::Attribute,
                );
            }
            "value" | "_value_" => {
                let value = member.value();
                if value.is_none() {
                    let result = Instance::new(enum_class, None).lookup_with_details(
                        i_s,
                        add_issue,
                        name,
                        LookupKind::OnlyType,
                    );
                    if result.lookup.is_some() {
                        return result;
                    }
                }
                return LookupDetails::new(
                    Type::Enum(member.enum_.clone()),
                    LookupResult::UnknownName(member.infer_value(i_s)),
                    AttributeKind::DefMethod { is_final: false },
                );
            }
            "_ignore_" => return LookupDetails::none(),
            _ => (),
        }
    }
    lookup_on_enum_instance_fallback(i_s, add_issue, &member.enum_, name)
}

fn lookup_members_or_aliases_on_enum(
    i_s: &InferenceState,
    enum_: &Arc<Enum>,
    name: &str,
) -> LookupResult {
    match Enum::lookup(enum_, i_s.db, name, true).or_else(|| {
        enum_.member_aliases.iter().find_map(|alias| {
            if alias.name.as_str(i_s.db) != name {
                return None;
            }
            Enum::lookup(enum_, i_s.db, alias.pointing_to_name.as_str(i_s.db), true)
        })
    }) {
        Some(m) => {
            if let Some(link) = m.member_definition().value {
                let node_ref = NodeRef::from_link(i_s.db, link);
                if node_ref.maybe_name().is_some() {
                    return LookupResult::GotoName {
                        name: link,
                        inf: Inferred::from_type(Type::EnumMember(m)),
                    };
                }
            }
            LookupResult::UnknownName(Inferred::from_type(Type::EnumMember(m)))
        }
        None => LookupResult::None,
    }
}
