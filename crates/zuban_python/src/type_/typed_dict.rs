use std::{
    hash::{Hash, Hasher},
    sync::{Arc, OnceLock},
};

use super::{
    CallableContent, CallableParam, CallableParams, CustomBehavior, DbString, FormatStyle,
    GenericsList, LookupResult, NeverCause, ParamType, RecursiveType, ReplaceTypeVarLikes,
    StringSlice, Type, TypeVarLikeUsage, TypeVarLikes, utils::method_with_fallback,
};
use crate::{
    arguments::{ArgKind, Args, InferredArg},
    database::{Database, PointLink},
    diagnostics::IssueKind,
    file::infer_string_index,
    format_data::{AvoidRecursionFor, FormatData},
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    match_::{Match, MismatchReason},
    matching::{ErrorStrs, LookupKind, Matcher, OnTypeError},
    new_class,
    result_context::ResultContext,
    type_::{StarStarParamType, Tuple},
    type_helpers::{Class, Instance, InstanceLookupOptions, LookupDetails},
    utils::join_with_commas,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypedDictMember {
    pub name: StringSlice,
    pub type_: Type,
    pub required: bool,
    pub read_only: bool,
}

pub(crate) struct TypedDictEntry<'x> {
    pub name: Option<StringSlice>,
    pub type_: &'x Type,
    pub required: bool,
    pub read_only: bool,
}

impl TypedDictMember {
    pub fn replace_type(&self, callable: impl FnOnce(&Type) -> Option<Type>) -> Self {
        Self {
            name: self.name,
            type_: callable(&self.type_).unwrap_or_else(|| self.type_.clone()),
            required: self.required,
            read_only: self.read_only,
        }
    }

    pub fn as_keyword_param(&self) -> CallableParam {
        CallableParam {
            type_: ParamType::KeywordOnly(self.type_.clone()),
            name: Some(DbString::StringSlice(self.name)),
            has_default: !self.required,
            might_have_type_vars: true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypedDictGenerics {
    None,
    NotDefinedYet(TypeVarLikes),
    Generics(GenericsList),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExtraItemsType {
    pub t: Type,
    pub read_only: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypedDictMembers {
    pub(crate) named: Box<[TypedDictMember]>,
    pub(crate) extra_items: Option<ExtraItemsType>,
}

#[derive(Debug, Clone, Eq)]
pub(crate) struct TypedDict {
    pub name: Option<StringSlice>,
    members: OnceLock<TypedDictMembers>,
    pub defined_at: PointLink,
    pub generics: TypedDictGenerics,
    pub is_final: bool,
}

impl TypedDict {
    pub fn new(
        name: Option<StringSlice>,
        members: TypedDictMembers,
        defined_at: PointLink,
        generics: TypedDictGenerics,
    ) -> Arc<Self> {
        Arc::new(Self {
            name,
            members: OnceLock::from(members),
            defined_at,
            generics,
            is_final: false,
        })
    }

    pub fn new_definition(
        name: StringSlice,
        members: TypedDictMembers,
        defined_at: PointLink,
        type_var_likes: TypeVarLikes,
    ) -> Arc<Self> {
        let generics = if type_var_likes.is_empty() {
            TypedDictGenerics::None
        } else {
            TypedDictGenerics::NotDefinedYet(type_var_likes)
        };
        Arc::new(Self {
            name: Some(name),
            members: OnceLock::from(members),
            defined_at,
            generics,
            is_final: false,
        })
    }

    pub fn new_class_definition(
        name: StringSlice,
        defined_at: PointLink,
        type_var_likes: TypeVarLikes,
        is_final: bool,
    ) -> Arc<Self> {
        let generics = if type_var_likes.is_empty() {
            TypedDictGenerics::None
        } else {
            TypedDictGenerics::NotDefinedYet(type_var_likes)
        };
        Arc::new(Self {
            name: Some(name),
            members: OnceLock::new(),
            defined_at,
            generics,
            is_final,
        })
    }

    pub fn late_initialization_of_members(&self, members: TypedDictMembers) {
        debug_assert!(!matches!(self.generics, TypedDictGenerics::Generics(_)));
        self.members.set(members).unwrap()
    }

    pub fn apply_generics(&self, db: &Database, generics: TypedDictGenerics) -> Arc<Self> {
        let mut members = OnceLock::new();
        if let TypedDictGenerics::Generics(generics) = &generics
            && let Some(ms) = self.members.get()
        {
            members = OnceLock::from(Self::remap_members_with_generics(db, ms, generics))
        }
        Arc::new(TypedDict {
            name: self.name,
            members,
            defined_at: self.defined_at,
            generics,
            is_final: self.is_final,
        })
    }

    fn remap_members_with_generics(
        db: &Database,
        original_members: &TypedDictMembers,
        generics: &GenericsList,
    ) -> TypedDictMembers {
        TypedDictMembers {
            named: original_members
                .named
                .iter()
                .map(|m| {
                    m.replace_type(|_| {
                        m.type_.replace_type_var_likes(db, &mut |usage| {
                            Some(generics[usage.index()].clone())
                        })
                    })
                })
                .collect(),
            extra_items: original_members
                .extra_items
                .as_ref()
                .map(|extra| ExtraItemsType {
                    t: extra
                        .t
                        .replace_type_var_likes(db, &mut |usage| {
                            Some(generics[usage.index()].clone())
                        })
                        .unwrap_or_else(|| extra.t.clone()),
                    read_only: extra.read_only,
                }),
        }
    }

    pub fn has_calculated_members(&self, db: &Database) -> bool {
        let members = self.members.get();
        if members.is_none() && matches!(&self.generics, TypedDictGenerics::Generics(_)) {
            // Generic TypedDicts can be remapped so we need to recheck the original definition if
            // there are calculated members.
            let class = Class::from_non_generic_link(db, self.defined_at);
            let original_typed_dict = class.maybe_typed_dict().unwrap();
            if original_typed_dict.has_calculated_members(db) {
                return true;
            }
        }
        members.is_some()
    }

    pub fn calculating(&self) -> bool {
        self.members.get().is_none()
    }

    pub fn members(&self, db: &Database) -> &TypedDictMembers {
        self.members.get().unwrap_or_else(|| {
            let TypedDictGenerics::Generics(list) = &self.generics else {
                unreachable!()
            };
            let class = Class::from_non_generic_link(db, self.defined_at);
            let original_typed_dict = class.maybe_typed_dict().unwrap();
            // The members are not pre-calculated, because there existed recursions where the
            // members of the original class were not calculated at that point. Therefore do that
            // now.
            let new_members = Self::remap_members_with_generics(
                db,
                original_typed_dict.members.get().unwrap(),
                list,
            );
            let result = self.members.set(new_members);
            debug_assert_eq!(result, Ok(()));
            self.members.get().unwrap()
        })
    }

    pub fn iter_required_members(
        &self,
        db: &Database,
    ) -> impl Iterator<Item = &'_ TypedDictMember> {
        self.members(db)
            .named
            .iter()
            .filter(|member| member.required)
    }

    pub fn iter_optional_members(
        &self,
        db: &Database,
    ) -> impl Iterator<Item = &'_ TypedDictMember> {
        self.members(db)
            .named
            .iter()
            .filter(|member| !member.required)
    }

    pub fn find_member(&self, db: &Database, name: &str) -> Option<&TypedDictMember> {
        self.members(db)
            .named
            .iter()
            .find(|p| p.name.as_str(db) == name)
    }

    pub fn find_entry(&self, db: &Database, name: &str) -> Option<TypedDictEntry<'_>> {
        let m = self.members(db);
        if let Some(member) = m.named.iter().find(|p| p.name.as_str(db) == name) {
            Some(TypedDictEntry {
                name: Some(member.name),
                type_: &member.type_,
                required: member.required,
                read_only: member.read_only,
            })
        } else {
            m.extra_items.as_ref().map(|e| TypedDictEntry {
                name: None,
                type_: &e.t,
                required: false,
                read_only: e.read_only,
            })
        }
    }

    fn qualified_name(&self, db: &Database) -> Option<String> {
        let name = self.name?;
        let module = db.loaded_python_file(name.file_index).qualified_name(db);
        Some(format!("{module}.{}", name.as_str(db)))
    }

    pub fn union(&self, i_s: &InferenceState, other: &Self) -> Type {
        let m1 = self.members(i_s.db);
        let m2 = other.members(i_s.db);
        let mut members: Vec<_> = m1.named.clone().into();
        'outer: for m2 in m2.named.iter() {
            for m1 in members.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db) {
                    if m1.required != m2.required
                        || m1.read_only != m2.read_only
                        || !m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                    {
                        return Type::Never(NeverCause::Other);
                    }
                    continue 'outer;
                }
            }
            members.push(m2.clone());
        }
        // TODO extra_items: handle
        Type::TypedDict(Self::new(
            None,
            TypedDictMembers {
                named: members.into_boxed_slice(),
                extra_items: None,
            },
            self.defined_at,
            TypedDictGenerics::None,
        ))
    }

    pub fn intersection(&self, i_s: &InferenceState, other: &Self) -> Arc<TypedDict> {
        let mut new_members = vec![];
        let ms1 = self.members(i_s.db);
        let ms2 = other.members(i_s.db);
        for m1 in ms1.named.iter() {
            for m2 in ms2.named.iter() {
                if m1.name.as_str(i_s.db) == m2.name.as_str(i_s.db)
                    && m1.required == m2.required
                    && m1.type_.is_simple_same_type(i_s, &m2.type_).bool()
                {
                    let mut new = m1.clone();
                    new.read_only |= m2.read_only;
                    new_members.push(new);
                }
            }
        }
        Self::new(
            None,
            TypedDictMembers {
                named: new_members.into_boxed_slice(),
                extra_items: ms1
                    .extra_items
                    .as_ref()
                    .zip(ms2.extra_items.as_ref())
                    .and_then(|(e1, e2)| {
                        if !e1.t.is_simple_same_type(i_s, &e2.t).bool() {
                            return None;
                        }
                        Some(ExtraItemsType {
                            t: e1.t.clone(),
                            read_only: e1.read_only || e2.read_only,
                        })
                    }),
            },
            self.defined_at,
            TypedDictGenerics::None,
        )
    }

    pub fn name_or_fallback(&self, format_data: &FormatData) -> String {
        if let Some(name) = self.name {
            let name = name.as_str(format_data.db);
            match &self.generics {
                TypedDictGenerics::Generics(list) => {
                    // Mypy seems to format TypedDicts with generics always with a qualified name.
                    let name = self
                        .qualified_name(format_data.db)
                        .unwrap_or_else(|| name.into());
                    format!("{name}[{}]", list.format(format_data))
                }
                _ => name.into(),
            }
        } else {
            self.format_full(format_data, None)
        }
    }

    pub fn format(&self, format_data: &FormatData) -> String {
        match format_data.style {
            FormatStyle::MypyRevealType => {
                self.format_full(format_data, self.qualified_name(format_data.db).as_deref())
            }
            FormatStyle::Short if !format_data.should_format_qualified(self.defined_at) => {
                self.name_or_fallback(format_data)
            }
            _ => self
                .qualified_name(format_data.db)
                .unwrap_or_else(|| self.name_or_fallback(format_data)),
        }
    }

    pub fn format_full(&self, format_data: &FormatData, name: Option<&str>) -> String {
        match format_data.with_seen_recursive_type(AvoidRecursionFor::TypedDict(self.defined_at)) {
            Ok(format_data) => {
                let m = self.members(format_data.db);
                let params = join_with_commas(m.named.iter().map(|p| {
                    format!(
                        "'{}'{}{}: {}",
                        p.name.as_str(format_data.db),
                        match p.required {
                            true => "",
                            false => "?",
                        },
                        match p.read_only {
                            true => "=",
                            false => "",
                        },
                        p.type_.format(&format_data)
                    )
                }));

                let rest = if let Some(e) = &m.extra_items {
                    if e.t.is_never() {
                        ", closed=True".to_string()
                    } else {
                        let mut inner = e.t.format(&format_data).into_string();
                        if e.read_only {
                            inner = format!("ReadOnly[{inner}]");
                        }
                        format!(", extra_items={inner}")
                    }
                } else {
                    "".to_string()
                };
                if let Some(name) = name {
                    format!("TypedDict('{name}', {{{params}}}{rest})")
                } else {
                    format!("TypedDict({{{params}}}{rest})")
                }
            }
            Err(()) => "...".to_string(),
        }
    }

    pub(crate) fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        add_issue: &dyn Fn(IssueKind),
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_string_index(
                i_s,
                simple,
                |key| {
                    Some({
                        if let Some(member) = self.find_entry(i_s.db, key) {
                            Inferred::from_type(member.type_.clone())
                        } else {
                            add_issue(IssueKind::TypedDictHasNoKeyForGet {
                                typed_dict: self.format(&FormatData::new_short(i_s.db)).into(),
                                key: key.into(),
                            });
                            Inferred::new_any_from_error()
                        }
                    })
                },
                || add_access_key_must_be_string_literal_issue(i_s.db, self, add_issue),
            ),
            _ => {
                add_access_key_must_be_string_literal_issue(i_s.db, self, add_issue);
                Inferred::new_any_from_error()
            }
        }
    }

    pub fn replace(
        &self,
        generics: TypedDictGenerics,
        mut callable: &mut impl FnMut(&Type) -> Option<Type>,
    ) -> Arc<Self> {
        Arc::new(TypedDict {
            name: self.name,
            members: if let Some(m) = self.members.get() {
                OnceLock::from(TypedDictMembers {
                    named: m
                        .named
                        .iter()
                        .map(|m| m.replace_type(&mut callable))
                        .collect::<Box<_>>(),
                    extra_items: m.extra_items.as_ref().map(|e| ExtraItemsType {
                        t: callable(&e.t).unwrap_or_else(|| e.t.clone()),
                        read_only: e.read_only,
                    }),
                })
            } else {
                OnceLock::new()
            },
            defined_at: self.defined_at,
            generics,
            is_final: self.is_final,
        })
    }

    pub fn with_any_generics(&self, db: &Database) -> Arc<Self> {
        let TypedDictGenerics::NotDefinedYet(type_var_likes) = &self.generics else {
            unreachable!()
        };
        let generics =
            TypedDictGenerics::Generics(type_var_likes.as_default_or_any_generic_list(db));
        self.replace(generics, &mut |t| {
            t.replace_type_var_likes(db, &mut |u| Some(u.as_default_or_any_generic_item(db)))
        })
    }

    pub fn matches(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        other: &Self,
        read_only: bool,
    ) -> Match {
        let mut matches = Match::new_true();
        let ms1 = self.members(i_s.db);
        for m1 in ms1.named.iter() {
            if let Some(m2) = other.find_entry(i_s.db, m1.name.as_str(i_s.db)) {
                // Required must match except if the wanted type is also read-only (and therefore
                // may not be modified afterwards
                if m1.required != m2.required && !(m1.read_only && !m1.required) {
                    return Match::new_false();
                }
                if !m1.read_only && m2.read_only {
                    return Match::new_false();
                }
                if m1.read_only {
                    matches &= m1.type_.is_super_type_of(i_s, matcher, m2.type_);
                } else {
                    // When matching mutable fields, the type must be the exact same, because
                    // modifications propagate from one to the other TypedDict.
                    matches &= m1.type_.is_same_type(i_s, matcher, m2.type_);
                }
            } else if !read_only || m1.required {
                return Match::new_false();
            }
        }
        if let Some(extra_items1) = &ms1.extra_items {
            let ms2 = other.members(i_s.db);
            if let Some(extra_items2) = &ms2.extra_items {
                matches &= if extra_items1.read_only {
                    extra_items1
                        .t
                        .is_super_type_of(i_s, matcher, &extra_items2.t)
                } else {
                    extra_items1.t.is_same_type(i_s, matcher, &extra_items2.t)
                }
            } else {
                return Match::new_false();
            }

            for m2 in ms2.named.iter() {
                if let Some(m1) = self.find_entry(i_s.db, m2.name.as_str(i_s.db))
                    && m1.name.is_none()
                {
                    if m2.required {
                        return Match::new_false();
                    }
                    matches &= if extra_items1.read_only {
                        m1.type_.is_super_type_of(i_s, matcher, &m2.type_)
                    } else {
                        m1.type_.is_same_type(i_s, matcher, &m2.type_)
                    }
                }
            }
        }
        matches
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        if let TypedDictGenerics::Generics(list) = &self.generics {
            list.search_type_vars(found_type_var)
        }
    }

    pub fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Arc<RecursiveType>>,
    ) -> bool {
        let m = self.members(i_s.db);
        m.named
            .iter()
            .any(|m| m.type_.has_any_internal(i_s, already_checked))
            || m.extra_items
                .as_ref()
                .is_some_and(|e| e.t.has_any_internal(i_s, already_checked))
    }

    fn can_be_emptied(&self, db: &Database) -> bool {
        let ms = self.members(db);
        ms.extra_items.as_ref().is_some_and(|e| !e.read_only)
            && ms.named.iter().all(|m| !m.required && !m.read_only)
    }

    pub fn has_required_members(&self, db: &Database) -> bool {
        let ms = self.members(db);
        ms.named.iter().any(|m| m.required)
    }

    pub fn can_be_overwritten_with(&self, i_s: &InferenceState) -> Option<&Type> {
        let ms = self.members(i_s.db);
        let e_t = ms.extra_items.as_ref()?;
        (!e_t.read_only
            && ms.named.iter().all(|m| {
                !m.required && !m.read_only && e_t.t.is_simple_same_type(i_s, &m.type_).bool()
            }))
        .then_some(&e_t.t)
    }

    pub fn has_extra_items(&self, db: &Database) -> bool {
        self.members(db).extra_items.is_some()
    }

    pub fn is_closed(&self, db: &Database) -> bool {
        self.members(db)
            .extra_items
            .as_ref()
            .is_some_and(|t| t.t.is_never())
    }

    pub fn union_of_all_types(&self, i_s: &InferenceState) -> Type {
        let ms = self.members(i_s.db);
        Type::simplified_union_from_iterators(
            i_s,
            ms.named
                .iter()
                .map(|m| &m.type_)
                .chain(ms.extra_items.as_ref().map(|t| &t.t)),
        )
    }
}

impl ExtraItemsType {
    pub fn format_as_param(&self, format_data: &FormatData) -> String {
        format!("**{}", self.t.format(format_data))
    }
}

pub fn rc_typed_dict_as_callable(db: &Database, slf: Arc<TypedDict>) -> CallableContent {
    CallableContent::new_simple(
        slf.name.map(DbString::StringSlice),
        None,
        slf.defined_at,
        match &slf.generics {
            TypedDictGenerics::None | TypedDictGenerics::Generics(_) => {
                db.python_state.empty_type_var_likes.clone()
            }
            TypedDictGenerics::NotDefinedYet(type_vars) => type_vars.clone(),
        },
        CallableParams::Simple({
            let ms = slf.members.get().unwrap();
            ms.named
                .iter()
                .map(|m| m.as_keyword_param())
                .chain(ms.extra_items.as_ref().map(|e| {
                    CallableParam::new_anonymous(ParamType::StarStar(StarStarParamType::ValueType(
                        e.t.clone(),
                    )))
                }))
                .collect()
        }),
        Type::TypedDict(slf.clone()),
    )
}

impl PartialEq for TypedDict {
    fn eq(&self, other: &Self) -> bool {
        self.defined_at == other.defined_at && self.generics == other.generics
    }
}

impl Hash for TypedDict {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.defined_at.hash(state);
        self.generics.hash(state);
    }
}

fn add_access_key_must_be_string_literal_issue(
    db: &Database,
    td: &TypedDict,
    add_issue: impl FnOnce(IssueKind),
) {
    add_issue(IssueKind::TypedDictAccessKeyMustBeStringLiteral {
        keys: join_with_commas(
            td.members(db)
                .named
                .iter()
                .map(|member| format!("\"{}\"", member.name.as_str(db))),
        )
        .into(),
    });
}

pub(crate) fn typed_dict_setdefault<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "setdefault",
        typed_dict_setdefault_internal,
    )
}

fn typed_dict_setdefault_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let mut iterator = args.iter(i_s.mode);
    let first_arg = iterator.next()?;
    let second_arg = iterator.next();
    if iterator.next().is_some() {
        return None;
    }
    let default = match &second_arg {
        Some(second) => match &second.kind {
            ArgKind::Positional(second) => second.infer(&mut ResultContext::Unknown),
            ArgKind::Keyword(second) if second.key == "default" => {
                second.infer(&mut ResultContext::Unknown)
            }
            _ => return None,
        },
        None => Inferred::new_none(),
    };

    let inferred_name = first_arg
        .clone()
        .maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let maybe_had_literals = inferred_name.run_on_str_literals(i_s, |key| {
        Some(Inferred::from_type({
            if let Some(member) = td.find_entry(i_s.db, key) {
                if !member
                    .type_
                    .is_simple_super_type_of(i_s, &default.as_cow_type(i_s))
                    .bool()
                {
                    let issue = IssueKind::TypedDictSetdefaultWrongDefaultType {
                        got: default.format_short(i_s),
                        expected: member.type_.format_short(i_s.db),
                    };
                    if let Some(second_arg) = second_arg.as_ref() {
                        second_arg.add_issue(i_s, issue);
                    } else {
                        args.add_issue(i_s, issue);
                    }
                }
                member.type_.clone()
            } else {
                first_arg.add_issue(
                    i_s,
                    IssueKind::TypedDictHasNoKey {
                        typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                        key: key.into(),
                    },
                );
                Type::ERROR
            }
        }))
    });

    if let Some(maybe_had_literals) = maybe_had_literals {
        Some(maybe_had_literals.simplified_union(i_s, default))
    } else {
        first_arg.add_issue(i_s, IssueKind::TypedDictKeysMustBeStringLiteral);
        Some(Inferred::new_any_from_error())
    }
}

pub(crate) fn typed_dict_get<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "get",
        typed_dict_get_internal,
    )
}

fn typed_dict_get_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    typed_dict_get_or_pop_internal(i_s, td, args, false)
}

fn typed_dict_get_or_pop_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
    is_pop: bool,
) -> Option<Inferred> {
    let mut iterator = args.iter(i_s.mode);
    let first_arg = iterator.next()?;
    let second_arg = iterator.next();
    if iterator.next().is_some() {
        return None;
    }
    let infer_default = |context: &mut _| match &second_arg {
        Some(second) => match &second.kind {
            ArgKind::Positional(second) => Some(second.infer(context)),
            ArgKind::Keyword(second) if second.key == "default" => Some(second.infer(context)),
            _ => None,
        },
        None => Some(Inferred::new_none()),
    };

    let inferred_name = first_arg
        .clone()
        .maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let maybe_had_literals = inferred_name.run_on_str_literals(i_s, |key| {
        Some(Inferred::from_type({
            if let Some(member) = td.find_entry(i_s.db, key) {
                if is_pop && (member.required || member.read_only) {
                    first_arg.add_issue(
                        i_s,
                        IssueKind::TypedDictKeyCannotBeDeleted {
                            typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                            key: key.into(),
                        },
                    );
                }
                member.type_.clone()
            } else if is_pop {
                first_arg.add_issue(
                    i_s,
                    IssueKind::TypedDictHasNoKey {
                        typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                        key: key.into(),
                    },
                );
                Type::ERROR
            } else {
                i_s.db.python_state.object_type()
            }
        }))
    });

    if let Some(maybe_had_literals) = maybe_had_literals {
        let default = infer_default(&mut ResultContext::new_known(
            &maybe_had_literals.as_cow_type(i_s),
        ))?;
        if is_pop && second_arg.is_none() {
            Some(maybe_had_literals)
        } else {
            Some(maybe_had_literals.simplified_union(i_s, default))
        }
    } else {
        let default = infer_default(&mut ResultContext::Unknown)?;
        let is_str_key = || {
            inferred_name
                .as_cow_type(i_s)
                .is_simple_same_type(i_s, &i_s.db.python_state.str_type())
                .bool()
        };
        if is_pop {
            if !(td.can_be_emptied(i_s.db) && is_str_key()) {
                first_arg.add_issue(i_s, IssueKind::TypedDictKeysMustBeStringLiteral);
            }
        } else if !is_str_key() {
            return None;
        }

        Some(
            if td.has_extra_items(i_s.db)
                && *inferred_name.as_cow_type(i_s) == i_s.db.python_state.str_type()
            {
                Inferred::from_type(
                    td.union_of_all_types(i_s)
                        .simplified_union(i_s, &default.as_cow_type(i_s)),
                )
            } else {
                Inferred::new_object(i_s.db)
            },
        )
    }
}

fn typed_dict_pop_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    typed_dict_get_or_pop_internal(i_s, td, args, true)
}

pub(crate) fn typed_dict_pop<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "pop",
        typed_dict_pop_internal,
    )
}

fn typed_dict_method_with_fallback<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    td: &TypedDict,
    name: &str,
    handler: fn(
        i_s: &InferenceState<'db, '_>,
        td: &TypedDict,
        args: &dyn Args<'db>,
    ) -> Option<Inferred>,
) -> Inferred {
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        name,
        handler,
        || Instance::new(i_s.db.python_state.typed_dict_class(), None),
    )
}

fn typed_dict_setitem<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "__setitem__",
        typed_dict_setitem_internal,
    )
}

fn typed_dict_setitem_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let mut iterator = args.iter(i_s.mode);
    let first_arg = iterator.next()?;
    let second_arg = iterator.next()?;
    if iterator.next().is_some() {
        return None;
    }
    let inf_key = first_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let value = second_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    if let Some(literal) = inf_key.maybe_string_literal(i_s) {
        let key = literal.as_str(i_s.db);
        if let Some(member) = td.find_entry(i_s.db, key) {
            if member.read_only {
                args.add_issue(
                    i_s,
                    IssueKind::TypedDictReadOnlyKeyMutated { key: key.into() },
                );
            }
            member.type_.error_if_not_matches(
                i_s,
                &value,
                |issue| args.add_issue(i_s, issue),
                |error_types| {
                    let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                    Some(IssueKind::TypedDictKeySetItemIncompatibleType {
                        key: key.into(),
                        got,
                        expected,
                    })
                },
            );
        } else {
            args.add_issue(
                i_s,
                IssueKind::TypedDictHasNoKey {
                    typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                    key: key.into(),
                },
            );
        }
    } else if let Some(expected) = td.can_be_overwritten_with(i_s)
        && inf_key
            .as_cow_type(i_s)
            .is_simple_same_type(i_s, &i_s.db.python_state.str_type())
            .bool()
    {
        expected.error_if_not_matches(
            i_s,
            &value,
            |issue| args.add_issue(i_s, issue),
            |error_types| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                Some(IssueKind::TypedDictSetItemWithExtraItemsMismatch { got, expected })
            },
        );
    } else {
        add_access_key_must_be_string_literal_issue(i_s.db, td, |issue| {
            args.add_issue(i_s, issue);
        })
    }
    Some(Inferred::new_none())
}

fn typed_dict_delitem<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "__delitem__",
        typed_dict_delitem_internal,
    )
}

fn typed_dict_delitem_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    typed_dict_get_or_pop_internal(i_s, td, args, true).map(|_| Inferred::new_none())
}

fn typed_dict_update<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::TypedDict(td) = bound.unwrap() else {
        unreachable!();
    };
    typed_dict_method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        td,
        "update",
        typed_dict_update_internal,
    )
}

fn typed_dict_update_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    td: &TypedDict,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let ms = td.members(i_s.db);
    let mut members: Vec<_> = ms.named.as_ref().into();
    for member in members.iter_mut() {
        member.required = false;
    }
    let expected = TypedDict::new(
        td.name,
        TypedDictMembers {
            named: members.into_boxed_slice(),
            extra_items: ms.extra_items.clone(),
        },
        td.defined_at,
        td.generics.clone(),
    );
    let inf = args.maybe_single_positional_arg(
        i_s,
        &mut ResultContext::new_known(&Type::TypedDict(expected)),
    )?;
    if let Type::TypedDict(from_arg) = inf.as_cow_type(i_s).as_ref() {
        let arg_members = from_arg.members(i_s.db);
        for member in arg_members.named.iter() {
            let name = member.name.as_str(i_s.db);
            if let Some(e) = td.find_entry(i_s.db, name)
                && e.read_only
                && !member.type_.is_never()
            {
                args.add_issue(
                    i_s,
                    IssueKind::TypedDictUpdateOfReadOnlyMember { name: name.into() },
                );
            }
        }
        let members = td.members(i_s.db);
        if let Some(arg_extra) = arg_members.extra_items.as_ref()
            && !arg_extra.t.is_never()
            && (members.named.iter().any(|m| m.read_only)
                || members
                    .extra_items
                    .as_ref()
                    .is_some_and(|extra| extra.read_only))
        {
            args.add_issue(
                i_s,
                IssueKind::TypedDictUpdateOfReadOnlyMember {
                    name: "extra_items".into(),
                },
            );
        }
    }
    Some(Inferred::new_none())
}

pub(crate) fn initialize_typed_dict<'db>(
    typed_dict: Arc<TypedDict>,
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Inferred {
    let mut iterator = args.iter(i_s.mode);
    let mut matcher = Matcher::new_typed_dict_matcher(&typed_dict);
    if let Some(first_arg) = iterator.next()
        && !first_arg.is_keyword_argument()
    {
        if let Some(next_arg) = iterator.next() {
            next_arg.add_issue(i_s, IssueKind::TypedDictWrongArgumentsInConstructor);
            return Inferred::new_any_from_error();
        }
        let InferredArg::Inferred(arg_inf) = first_arg.infer(&mut ResultContext::WithMatcher {
            matcher: &mut matcher,
            type_: &Type::TypedDict(typed_dict.clone()),
        }) else {
            first_arg.add_issue(i_s, IssueKind::TypedDictWrongArgumentsInConstructor);
            return Inferred::new_any_from_error();
        };
        match arg_inf.as_cow_type(i_s).as_ref() {
            Type::TypedDict(arg_td) => {
                if arg_td.defined_at != typed_dict.defined_at
                    && !typed_dict.matches(i_s, &mut matcher, arg_td, false).bool()
                {
                    first_arg.add_issue(i_s, IssueKind::TypedDictWrongArgumentsInConstructor);
                    return Inferred::new_any_from_error();
                }
            }
            _ => {
                first_arg.add_issue(i_s, IssueKind::TypedDictWrongArgumentsInConstructor);
                return Inferred::new_any_from_error();
            }
        }
    } else {
        check_typed_dict_call(i_s, &mut matcher, typed_dict.clone(), args);
    };
    let td = if matcher.has_type_var_matcher() {
        let generics = matcher
            .into_type_arguments(i_s, typed_dict.defined_at, true)
            .type_arguments_into_generics(i_s.db);
        typed_dict.apply_generics(i_s.db, TypedDictGenerics::Generics(generics.unwrap()))
    } else {
        typed_dict.clone()
    };
    Inferred::from_type(Type::TypedDict(td))
}

pub(crate) fn lookup_on_typed_dict<'a>(
    td: Arc<TypedDict>,
    i_s: &'a InferenceState,
    add_issue: &dyn Fn(IssueKind),
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    fn as_callable_without_params<'a>(
        db: &'a Database,
        td: Arc<TypedDict>,
        name: &'static str,
        return_type: Type,
    ) -> LookupDetails<'a> {
        let defined_at = td.defined_at;
        let name1 = Some(DbString::Static(name));
        LookupDetails::new(
            Type::TypedDict(td),
            LookupResult::UnknownName(Inferred::from_type(Type::Callable(Arc::new(
                CallableContent::new_non_generic(db, name1, None, defined_at, [], return_type),
            )))),
            AttributeKind::DefMethod { is_final: false },
        )
    }
    let bound = || Arc::new(Type::TypedDict(td.clone()));
    let lookup = LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(match name {
        "get" => CustomBehavior::new_method(typed_dict_get, Some(bound())),
        "setdefault" => CustomBehavior::new_method(typed_dict_setdefault, Some(bound())),
        "pop" => CustomBehavior::new_method(typed_dict_pop, Some(bound())),
        "__setitem__" => CustomBehavior::new_method(typed_dict_setitem, Some(bound())),
        "__delitem__" => CustomBehavior::new_method(typed_dict_delitem, Some(bound())),
        "update" => CustomBehavior::new_method(typed_dict_update, Some(bound())),
        "clear" if td.can_be_emptied(i_s.db) => {
            // Return an empty Callable
            return as_callable_without_params(i_s.db, td, "clear", Type::None);
        }
        "popitem" if td.can_be_emptied(i_s.db) => {
            let return_type = Type::Tuple(Tuple::new_fixed_length(
                [i_s.db.python_state.str_type(), td.union_of_all_types(i_s)].into(),
            ));
            return as_callable_without_params(i_s.db, td, "popitem", return_type);
        }
        "items" if td.has_extra_items(i_s.db) => {
            let return_type = new_class!(
                i_s.db.python_state.list_link(),
                Type::Tuple(Tuple::new_fixed_length(
                    [i_s.db.python_state.str_type(), td.union_of_all_types(i_s)].into(),
                ))
            );
            return as_callable_without_params(i_s.db, td, "items", return_type);
        }
        "values" if td.has_extra_items(i_s.db) => {
            let return_type =
                new_class!(i_s.db.python_state.list_link(), td.union_of_all_types(i_s),);
            return as_callable_without_params(i_s.db, td, "values", return_type);
        }
        _ => {
            return Instance::new(i_s.db.python_state.typed_dict_class(), None).lookup(
                i_s,
                name,
                InstanceLookupOptions::new(add_issue)
                    .with_kind(kind)
                    .with_as_self_instance(&|| Type::TypedDict(td.clone())),
            );
        }
    })));
    LookupDetails::new(
        Type::TypedDict(td),
        lookup,
        AttributeKind::DefMethod { is_final: false },
    )
}

pub(crate) fn infer_typed_dict_arg(
    i_s: &InferenceState,
    typed_dict: &TypedDict,
    matcher: &mut Matcher,
    maybe_add_issue: impl Fn(IssueKind) -> bool,
    key: &str,
    extra_keys: &mut Vec<String>,
    infer: impl FnOnce(&mut ResultContext) -> Inferred,
) {
    if let Some(member) = typed_dict.find_entry(i_s.db, key) {
        let inferred = infer(&mut ResultContext::WithMatcher {
            type_: member.type_,
            matcher,
        });

        member.type_.error_if_not_matches_with_matcher(
            i_s,
            matcher,
            &inferred,
            maybe_add_issue,
            |error_types, _: &MismatchReason| {
                let ErrorStrs { expected, got } = error_types.as_boxed_strs(i_s.db);
                Some(IssueKind::TypedDictIncompatibleType {
                    key: key.into(),
                    got,
                    expected,
                })
            },
        );
    } else {
        extra_keys.push(key.into())
    }
}

pub(crate) fn check_typed_dict_call<'db>(
    i_s: &InferenceState<'db, '_>,
    matcher: &mut Matcher,
    typed_dict: Arc<TypedDict>,
    args: &dyn Args<'db>,
) -> Option<Type> {
    let mut extra_keys = vec![];
    for arg in args.iter(i_s.mode) {
        if let Some(key) = arg.keyword_name(i_s.db) {
            infer_typed_dict_arg(
                i_s,
                &typed_dict,
                matcher,
                |issue| arg.add_issue(i_s, issue),
                key,
                &mut extra_keys,
                |context| arg.infer_inferrable(i_s, context),
            );
        } else {
            arg.add_issue(
                i_s,
                IssueKind::ArgumentIssue(
                    format!(
                        "Unexpected argument to \"{}\"",
                        typed_dict.name_or_fallback(&FormatData::new_short(i_s.db))
                    )
                    .into(),
                ),
            );
            return None;
        }
    }
    maybe_add_extra_keys_issue(
        i_s.db,
        &typed_dict,
        |issue| args.add_issue(i_s, issue),
        extra_keys,
    );
    let mut missing_keys: Vec<Box<str>> = vec![];
    let m = typed_dict.members(i_s.db);
    for member in m.named.iter() {
        if member.required {
            let expected_name = member.name.as_str(i_s.db);
            if !args
                .iter(i_s.mode)
                .any(|arg| arg.keyword_name(i_s.db) == Some(expected_name))
            {
                missing_keys.push(expected_name.into())
            }
        }
    }
    if !missing_keys.is_empty() {
        args.add_issue(
            i_s,
            IssueKind::TypedDictMissingKeys {
                typed_dict: typed_dict
                    .name_or_fallback(&FormatData::new_short(i_s.db))
                    .into(),
                keys: missing_keys.into(),
            },
        );
    }
    Some(if matches!(&typed_dict.generics, TypedDictGenerics::None) {
        Type::TypedDict(typed_dict)
    } else {
        matcher
            .replace_type_var_likes_for_unknown_type_vars(i_s.db, &Type::TypedDict(typed_dict))
            .into_owned()
    })
}

pub(crate) fn maybe_add_extra_keys_issue(
    db: &Database,
    typed_dict: &TypedDict,
    add_issue: impl Fn(IssueKind) -> bool,
    mut extra_keys: Vec<String>,
) {
    add_issue(IssueKind::TypedDictExtraKey {
        key: match extra_keys.len() {
            0 => return,
            1 => format!("\"{}\"", extra_keys.remove(0)).into(),
            _ => format!(
                "({})",
                join_with_commas(extra_keys.iter().map(|key| format!("\"{key}\"")))
            )
            .into(),
        },
        typed_dict: typed_dict
            .name_or_fallback(&FormatData::new_short(db))
            .into(),
    });
}
