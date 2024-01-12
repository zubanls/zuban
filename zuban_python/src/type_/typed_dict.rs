use std::{cell::OnceCell, rc::Rc};

use parsa_python_ast::{AtomContent, DictElement};

use super::{
    replace::ReplaceTypeVarLike, utils::method_with_fallback, AnyCause, CallableParam,
    CustomBehavior, DbString, FormatStyle, GenericsList, ParamType, ReplaceSelf, StringSlice, Type,
    TypeVarLikes,
};
use crate::{
    arguments::{ArgKind, Args},
    database::{ComplexPoint, Database, PointLink, TypedDictDefinition},
    diagnostics::IssueType,
    file::{infer_string_index, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn},
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        AvoidRecursionFor, FormatData, LookupKind, LookupResult, Match, Matcher, MismatchReason,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    type_helpers::{Class, Instance, LookupDetails, Module},
    utils::join_with_commas,
};

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

    pub fn as_keyword_param(&self) -> CallableParam {
        CallableParam {
            type_: ParamType::KeywordOnly(self.type_.clone()),
            name: Some(DbString::StringSlice(self.name)),
            has_default: !self.required,
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
    members: OnceCell<Box<[TypedDictMember]>>,
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
            members: OnceCell::from(members),
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
            members: OnceCell::from(members),
            defined_at,
            generics,
        })
    }

    pub fn new_class_definition(
        name: StringSlice,
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
            members: OnceCell::new(),
            defined_at,
            generics,
        })
    }

    pub fn late_initialization_of_members(&self, members: Box<[TypedDictMember]>) {
        debug_assert!(!matches!(self.generics, TypedDictGenerics::Generics(_)));
        self.members.set(members).unwrap()
    }

    pub fn apply_generics(&self, db: &Database, generics: GenericsList) -> Rc<Self> {
        let members = if let Some(members) = self.members.get() {
            OnceCell::from(Self::remap_members_with_generics(db, members, &generics))
        } else {
            OnceCell::new()
        };
        Rc::new(TypedDict {
            name: self.name,
            members,
            defined_at: self.defined_at,
            generics: TypedDictGenerics::Generics(generics),
        })
    }

    fn remap_members_with_generics(
        db: &Database,
        original_members: &[TypedDictMember],
        generics: &GenericsList,
    ) -> Box<[TypedDictMember]> {
        original_members
            .iter()
            .map(|m| {
                m.replace_type(|t| {
                    m.type_
                        .replace_type_var_likes(db, &mut |usage| generics[usage.index()].clone())
                })
            })
            .collect()
    }

    pub fn maybe_calculated_members(&self, db: &Database) -> Option<&[TypedDictMember]> {
        let members = self.members.get().map(|m| m.as_ref());
        if members.is_none() {
            if let TypedDictGenerics::Generics(list) = &self.generics {
                let class = Class::from_non_generic_link(db, self.defined_at);
                let original_typed_dict = class.maybe_typed_dict().unwrap();
                if original_typed_dict.maybe_calculated_members(db).is_some() {
                    return Some(self.members(db));
                }
            }
        }
        members
    }

    pub fn calculating(&self) -> bool {
        self.members.get().is_none()
    }

    pub fn members(&self, db: &Database) -> &[TypedDictMember] {
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

    pub fn find_member(&self, db: &Database, name: &str) -> Option<&TypedDictMember> {
        self.members(db).iter().find(|p| p.name.as_str(db) == name)
    }

    fn qualified_name(&self, db: &Database) -> Option<String> {
        let Some(name) = self.name else {
            return None
        };
        let module = Module::from_file_index(db, name.file_index).qualified_name(db);
        Some(format!("{module}.{}", name.as_str(db)))
    }

    pub fn union(&self, i_s: &InferenceState, other: &Self) -> Type {
        let mut members: Vec<_> = self.members(i_s.db).clone().into();
        'outer: for m2 in other.members(i_s.db).iter() {
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
        for m1 in self.members(i_s.db).iter() {
            for m2 in other.members(i_s.db).iter() {
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
            let name = name.as_str(format_data.db);
            match &self.generics {
                TypedDictGenerics::Generics(list) => {
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
            FormatStyle::Short if !format_data.verbose => self.name_or_fallback(format_data),
            _ => self
                .qualified_name(format_data.db)
                .unwrap_or_else(|| todo!()),
        }
    }

    pub fn format_full(&self, format_data: &FormatData, name: Option<&str>) -> String {
        let rec = AvoidRecursionFor::TypedDict(self.defined_at);
        if format_data.has_already_seen_recursive_type(rec) {
            return "...".to_string();
        }
        let format_data = &format_data.with_seen_recursive_type(rec);
        let params = join_with_commas(self.members(format_data.db).iter().map(|p| {
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

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        add_errors: bool,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_string_index(
                i_s,
                simple,
                |key| {
                    Some({
                        if let Some(member) = self.find_member(i_s.db, key) {
                            Inferred::from_type(member.type_.clone())
                        } else {
                            if add_errors {
                                simple.as_node_ref().add_issue(
                                    i_s,
                                    IssueType::TypedDictHasNoKeyForGet {
                                        typed_dict: self
                                            .format(&FormatData::new_short(i_s.db))
                                            .into(),
                                        key: key.into(),
                                    },
                                );
                            }
                            Inferred::new_any_from_error()
                        }
                    })
                },
                || {
                    if add_errors {
                        add_access_key_must_be_string_literal_issue(i_s.db, self, |issue| {
                            slice_type.as_node_ref().add_issue(i_s, issue)
                        })
                    }
                },
            ),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
    }

    pub fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        generics: TypedDictGenerics,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Rc<Self> {
        Rc::new(TypedDict {
            name: self.name,
            members: if let Some(members) = self.members.get() {
                OnceCell::from(
                    members
                        .iter()
                        .map(|m| {
                            m.replace_type(|t| {
                                t.replace_type_var_likes_and_self(db, callable, replace_self)
                            })
                        })
                        .collect::<Box<_>>(),
                )
            } else {
                OnceCell::new()
            },
            defined_at: self.defined_at,
            generics,
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
        for m1 in self.members(i_s.db).iter() {
            if let Some(m2) = other.find_member(i_s.db, m1.name.as_str(i_s.db)) {
                if m1.required != m2.required {
                    return Match::new_false();
                }
                matches &= m1.type_.is_same_type(i_s, matcher, &m2.type_);
            } else {
                if !read_only || m1.required {
                    return Match::new_false();
                }
            }
        }
        matches
    }
}

#[derive(Default)]
pub struct TypedDictMemberGatherer {
    members: Vec<TypedDictMember>,
    first_after_merge_index: usize,
}

impl TypedDictMemberGatherer {
    pub(crate) fn add(&mut self, db: &Database, member: TypedDictMember) -> Result<(), IssueType> {
        let key = member.name.as_str(db);
        if let Some((i, m)) = self
            .members
            .iter_mut()
            .enumerate()
            .find(|(_, m)| m.name.as_str(db) == key)
        {
            if i >= self.first_after_merge_index {
                Err(IssueType::TypedDictDuplicateKey { key: key.into() })
            } else {
                *m = member;
                Err(IssueType::TypedDictOverwritingKeyWhileExtending { key: key.into() })
            }
        } else {
            self.members.push(member);
            Ok(())
        }
    }

    pub fn merge(&mut self, i_s: &InferenceState, node_ref: NodeRef, slice: &[TypedDictMember]) {
        for to_add in slice.iter() {
            let key = to_add.name.as_str(i_s.db);
            if let Some(current) = self
                .members
                .iter_mut()
                .find(|m| m.name.as_str(i_s.db) == key)
            {
                node_ref.add_issue(
                    i_s,
                    IssueType::TypedDictOverwritingKeyWhileMerging { key: key.into() },
                );
                *current = to_add.clone(); // Mypy prioritizes this...
            } else {
                self.members.push(to_add.clone());
            }
        }
        self.first_after_merge_index = self.members.len();
    }

    pub fn into_boxed_slice(self) -> Box<[TypedDictMember]> {
        self.members.into_boxed_slice()
    }
}

fn add_access_key_must_be_string_literal_issue(
    db: &Database,
    td: &TypedDict,
    add_issue: impl FnOnce(IssueType),
) {
    add_issue(IssueType::TypedDictAccessKeyMustBeStringLiteral {
        keys: join_with_commas(
            td.members(db)
                .iter()
                .map(|member| format!("\"{}\"", member.name.as_str(db))),
        )
        .into(),
    })
}

pub(crate) fn new_typed_dict<'db>(i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Inferred {
    new_typed_dict_internal(i_s, args).unwrap_or_else(Inferred::new_any_from_error)
}

fn new_typed_dict_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let mut iterator = args.iter();
    let Some(first_arg) = iterator.next() else {
        todo!()
    };
    let ArgKind::Positional(first) = first_arg.kind else {
        args.add_issue(i_s, IssueType::UnexpectedArgumentsToTypedDict);
        return None
    };
    let expr = first.node_ref.as_named_expression().expression();
    let Some(name) = StringSlice::from_string_in_expression(first.node_ref.file_index(), expr) else {
        first.node_ref.add_issue(i_s, IssueType::TypedDictFirstArgMustBeString);
        return None
    };

    if let Some(definition_name) = expr
        .maybe_single_string_literal()
        .unwrap()
        .in_simple_assignment()
    {
        let name = name.as_str(i_s.db);
        if name != definition_name.as_code() {
            first.node_ref.add_issue(
                i_s,
                IssueType::TypedDictNameMismatch {
                    string_name: Box::from(name),
                    variable_name: Box::from(definition_name.as_code()),
                },
            );
        }
    } else {
        todo!()
    }

    let Some(second_arg) = iterator.next() else {
        args.add_issue(i_s, IssueType::TooFewArguments(" for TypedDict()".into()));
        return None
    };
    let ArgKind::Positional(second) = second_arg.kind else {
        todo!()
    };
    let Some(atom_content) = second.node_ref.as_named_expression().expression().maybe_unpacked_atom() else {
        todo!()
    };
    let mut total = true;
    if let Some(next) = iterator.next() {
        match &next.kind {
            ArgKind::Keyword { key: "total", .. } => {
                total = infer_typed_dict_total_argument(
                    i_s,
                    next.infer(i_s, &mut ResultContext::Unknown),
                    |issue| next.add_issue(i_s, issue),
                )?;
            }
            ArgKind::Keyword { key, node_ref, .. } => {
                let s = format!(r#"Unexpected keyword argument "{key}" for "TypedDict""#);
                node_ref.add_issue(i_s, IssueType::ArgumentIssue(s.into()));
                return None;
            }
            _ => {
                args.add_issue(i_s, IssueType::UnexpectedArgumentsToTypedDict);
                return None;
            }
        };
    }
    if iterator.next().is_some() {
        args.add_issue(i_s, IssueType::TooManyArguments(" for \"TODO()\"".into()));
        return None;
    }
    let dct_iterator = match atom_content {
        AtomContent::Dict(dct) => dct.iter_elements(),
        _ => {
            second
                .node_ref
                .add_issue(i_s, IssueType::TypedDictSecondArgMustBeDict);
            return None;
        }
    };
    let on_type_var = &mut |i_s: &InferenceState, _: &_, _, _| TypeVarCallbackReturn::NotFound;
    let mut inference = first.node_ref.file.inference(i_s);
    let mut comp = TypeComputation::new(
        &mut inference,
        first.node_ref.as_link(),
        on_type_var,
        TypeComputationOrigin::TypedDictMember,
    );
    let mut members = TypedDictMemberGatherer::default();
    for element in dct_iterator {
        match element {
            DictElement::KeyValue(key_value) => {
                let Some(name) = StringSlice::from_string_in_expression(first.node_ref.file_index(), key_value.key()) else {
                    NodeRef::new(first.node_ref.file, key_value.key().index())
                        .add_issue(i_s, IssueType::TypedDictInvalidFieldName);
                    return None
                };
                if let Err(issue) = members.add(
                    i_s.db,
                    comp.compute_typed_dict_member(name, key_value.value(), total),
                ) {
                    NodeRef::new(first.node_ref.file, key_value.key().index())
                        .add_issue(i_s, issue);
                }
                key_value.key();
            }
            DictElement::Star(d) => {
                NodeRef::new(first.node_ref.file, d.index())
                    .add_issue(i_s, IssueType::TypedDictInvalidFieldName);
                return None;
            }
        };
    }

    let type_var_likes = comp.into_type_vars(|_, _| ());
    Some(Inferred::new_unsaved_complex(
        ComplexPoint::TypedDictDefinition(TypedDictDefinition::new(
            TypedDict::new_definition(
                name,
                members.into_boxed_slice(),
                first.node_ref.as_link(),
                type_var_likes,
            ),
            total,
        )),
    ))
}

pub(crate) fn infer_typed_dict_total_argument(
    i_s: &InferenceState,
    inf: Inferred,
    add_issue: impl Fn(IssueType),
) -> Option<bool> {
    if let Some(total) = inf.maybe_bool_literal(i_s) {
        Some(total)
    } else {
        add_issue(IssueType::TypedDictTotalMustBeTrueOrFalse);
        None
    }
}

pub(crate) fn typed_dict_setdefault<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
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
    let mut iterator = args.iter();
    let first_arg = iterator.next()?;
    let second_arg = iterator.next();
    if iterator.next().is_some() {
        return None;
    }
    let default = match &second_arg {
        Some(second) => match &second.kind {
            ArgKind::Positional { .. } | ArgKind::Keyword { key: "default", .. } => {
                second.infer(i_s, &mut ResultContext::Unknown)
            }
            _ => return None,
        },
        None => Inferred::new_none(),
    };

    let inferred_name = first_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let maybe_had_literals = inferred_name.run_on_str_literals(i_s, |key| {
        Some(Inferred::from_type({
            if let Some(member) = td.find_member(i_s.db, key) {
                if !member
                    .type_
                    .is_simple_super_type_of(i_s, &default.as_cow_type(i_s))
                    .bool()
                {
                    args.add_issue(
                        i_s,
                        IssueType::TypedDictSetdefaultWrongDefaultType {
                            got: default.format_short(i_s),
                            expected: member.type_.format_short(i_s.db),
                        },
                    )
                }
                member.type_.clone()
            } else {
                i_s.db.python_state.object_type()
            }
        }))
    });

    if let Some(maybe_had_literals) = maybe_had_literals {
        Some(maybe_had_literals.simplified_union(i_s, default))
    } else {
        Some(Inferred::from_type(i_s.db.python_state.object_type()))
    }
}

pub(crate) fn typed_dict_get<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
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
    let mut iterator = args.iter();
    let first_arg = iterator.next()?;
    let second_arg = iterator.next();
    if iterator.next().is_some() {
        return None;
    }
    let infer_default = |context: &mut _| match &second_arg {
        Some(second) => match &second.kind {
            ArgKind::Positional { .. } | ArgKind::Keyword { key: "default", .. } => {
                Some(second.infer(i_s, context))
            }
            _ => return None,
        },
        None => Some(Inferred::new_none()),
    };

    let inferred_name = first_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let maybe_had_literals = inferred_name.run_on_str_literals(i_s, |key| {
        Some(Inferred::from_type({
            if let Some(member) = td.find_member(i_s.db, key) {
                if is_pop && member.required {
                    args.add_issue(
                        i_s,
                        IssueType::TypedDictKeyCannotBeDeleted {
                            typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                            key: key.into(),
                        },
                    )
                }
                member.type_.clone()
            } else {
                if is_pop {
                    args.add_issue(
                        i_s,
                        IssueType::TypedDictHasNoKey {
                            typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                            key: key.into(),
                        },
                    );
                    Type::Any(AnyCause::FromError)
                } else {
                    i_s.db.python_state.object_type()
                }
            }
        }))
    });

    if let Some(maybe_had_literals) = maybe_had_literals {
        let default = infer_default(&mut ResultContext::Known(
            &maybe_had_literals.as_cow_type(i_s),
        ))?;
        if is_pop && second_arg.is_none() {
            Some(maybe_had_literals)
        } else {
            Some(maybe_had_literals.simplified_union(i_s, default))
        }
    } else {
        if is_pop {
            args.add_issue(i_s, IssueType::TypedDictKeysMustBeStringLiteral);
        }
        infer_default(&mut ResultContext::Unknown)?;
        Some(Inferred::from_type(i_s.db.python_state.object_type()))
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
    on_type_error: OnTypeError<'db, '_>,
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
    on_type_error: OnTypeError<'db, '_>,
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
    on_type_error: OnTypeError<'db, '_>,
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
    let mut iterator = args.iter();
    let first_arg = iterator.next()?;
    let second_arg = iterator.next()?;
    if iterator.next().is_some() {
        return None;
    }
    let inf_key = first_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    let value = second_arg.maybe_positional_arg(i_s, &mut ResultContext::Unknown)?;
    if let Some(literal) = inf_key.maybe_string_literal(i_s) {
        let key = literal.as_str(i_s.db);
        if let Some(member) = td.find_member(i_s.db, key) {
            member.type_.error_if_not_matches(
                i_s,
                &value,
                |issue| args.add_issue(i_s, issue),
                |got, expected| {
                    Some(IssueType::TypedDictKeySetItemIncompatibleType {
                        key: key.into(),
                        got,
                        expected,
                    })
                },
            );
        } else {
            args.add_issue(
                i_s,
                IssueType::TypedDictHasNoKey {
                    typed_dict: td.format(&FormatData::new_short(i_s.db)).into(),
                    key: key.into(),
                },
            );
        }
    } else {
        add_access_key_must_be_string_literal_issue(i_s.db, td, |issue| args.add_issue(i_s, issue))
    }
    Some(Inferred::new_none())
}

fn typed_dict_delitem<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
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
    on_type_error: OnTypeError<'db, '_>,
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
    let mut members: Vec<_> = td.members(i_s.db).clone().into();
    for member in members.iter_mut() {
        member.required = false;
    }
    let expected = TypedDict::new(
        td.name,
        members.into_boxed_slice(),
        td.defined_at,
        td.generics.clone(),
    );
    let inf_key = args
        .maybe_single_positional_arg(i_s, &mut ResultContext::Known(&Type::TypedDict(expected)))?;
    Some(Inferred::new_none())
}

pub(crate) fn initialize_typed_dict<'db>(
    typed_dict: Rc<TypedDict>,
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
) -> Inferred {
    let mut iterator = args.iter();
    let td = if let Some(first_arg) = iterator.next().filter(|arg| !arg.is_keyword_argument()) {
        if let Some(next_arg) = iterator.next() {
            next_arg.add_issue(i_s, IssueType::TypedDictWrongArgumentsInConstructor);
            return Inferred::new_any_from_error();
        }
        first_arg.infer(
            i_s,
            &mut ResultContext::Known(&Type::TypedDict(typed_dict.clone())),
        );
        typed_dict.clone()
    } else {
        let mut matcher = Matcher::new_typed_dict_matcher(&typed_dict);
        check_typed_dict_call(i_s, &mut matcher, typed_dict.clone(), args);
        if matcher.has_type_var_matcher() {
            let TypedDictGenerics::NotDefinedYet(type_var_likes) = &typed_dict.generics else {
                unreachable!();
            };
            let generics = matcher.into_generics_list(i_s.db, type_var_likes).unwrap();
            typed_dict.apply_generics(i_s.db, generics)
        } else {
            typed_dict.clone()
        }
    };
    Inferred::from_type(Type::TypedDict(td))
}

pub(crate) fn lookup_on_typed_dict<'a>(
    typed_dict: Rc<TypedDict>,
    i_s: &'a InferenceState,
    add_issue: impl Fn(IssueType),
    name: &str,
    kind: LookupKind,
) -> LookupDetails<'a> {
    let bound = || Rc::new(Type::TypedDict(typed_dict.clone()));
    let lookup = LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(match name {
        "get" => CustomBehavior::new_method(typed_dict_get, Some(bound())),
        "setdefault" => CustomBehavior::new_method(typed_dict_setdefault, Some(bound())),
        "pop" => CustomBehavior::new_method(typed_dict_pop, Some(bound())),
        "__setitem__" => CustomBehavior::new_method(typed_dict_setitem, Some(bound())),
        "__delitem__" => CustomBehavior::new_method(typed_dict_delitem, Some(bound())),
        "update" => CustomBehavior::new_method(typed_dict_update, Some(bound())),
        _ => {
            return Instance::new(i_s.db.python_state.typed_dict_class(), None)
                .lookup_with_explicit_self_binding(i_s, &add_issue, name, kind, 0, || {
                    Type::TypedDict(typed_dict.clone())
                })
        }
    })));
    LookupDetails::new(
        Type::TypedDict(typed_dict),
        lookup,
        AttributeKind::DefMethod,
    )
}

pub(crate) fn infer_typed_dict_item(
    i_s: &InferenceState,
    typed_dict: &TypedDict,
    matcher: &mut Matcher,
    add_issue: impl Fn(IssueType),
    key: &str,
    extra_keys: &mut Vec<String>,
    infer: impl FnOnce(&mut ResultContext) -> Inferred,
) {
    if let Some(member) = typed_dict.find_member(i_s.db, key) {
        let inferred = infer(&mut ResultContext::WithMatcher {
            type_: &member.type_,
            matcher,
        });

        member.type_.error_if_not_matches_with_matcher(
            i_s,
            matcher,
            &inferred,
            add_issue,
            |got, expected, _: &MismatchReason| {
                Some(IssueType::TypedDictIncompatibleType {
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
    typed_dict: Rc<TypedDict>,
    args: &dyn Args<'db>,
) -> Option<Type> {
    let mut extra_keys = vec![];
    for arg in args.iter() {
        if let Some(key) = arg.keyword_name(i_s.db) {
            infer_typed_dict_item(
                i_s,
                &typed_dict,
                matcher,
                |issue| arg.add_issue(i_s, issue),
                key,
                &mut extra_keys,
                |context| arg.infer(i_s, context),
            );
        } else {
            todo!()
        }
    }
    maybe_add_extra_keys_issue(
        i_s.db,
        &typed_dict,
        |issue| args.add_issue(i_s, issue),
        extra_keys,
    );
    let mut missing_keys: Vec<Box<str>> = vec![];
    for member in typed_dict.members(i_s.db).iter() {
        if member.required {
            let expected_name = member.name.as_str(i_s.db);
            if !args
                .iter()
                .any(|arg| arg.keyword_name(i_s.db) == Some(expected_name))
            {
                missing_keys.push(expected_name.into())
            }
        }
    }
    if !missing_keys.is_empty() {
        args.add_issue(
            i_s,
            IssueType::TypedDictMissingKeys {
                typed_dict: typed_dict
                    .name_or_fallback(&FormatData::new_short(i_s.db))
                    .into(),
                keys: missing_keys.into(),
            },
        )
    }
    Some(Type::TypedDict(typed_dict))
}

pub(crate) fn maybe_add_extra_keys_issue(
    db: &Database,
    typed_dict: &TypedDict,
    add_issue: impl Fn(IssueType),
    mut extra_keys: Vec<String>,
) {
    add_issue(IssueType::TypedDictExtraKey {
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
    })
}
