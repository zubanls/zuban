use std::sync::Arc;

use parsa_python_cst::{Annotation, AtomContent, DictElement, Expression};

use crate::{
    arguments::{ArgKind, Args},
    database::Database,
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    node_ref::NodeRef,
    recoverable_error,
    type_::{GenericsList, StringSlice, Type, TypedDict, TypedDictGenerics, TypedDictMember},
};

use super::{
    TypeComputation, TypeComputationOrigin, TypeContent, TypedDictFieldModifier,
    TypedDictFieldModifiers, UnknownCause, type_computation_for_variable_annotation,
};

impl<'db: 'file, 'file, 'i_s, 'c> TypeComputation<'db, 'file, 'i_s, 'c> {
    pub fn compute_typed_dict_member(
        &mut self,
        name: StringSlice,
        expr: Expression,
        total: bool,
    ) -> TypedDictMember {
        let calculated = self.compute_type(expr).remove_annotated();
        let mut required = total;
        let mut read_only = false;
        let type_ = match calculated {
            TypeContent::TypedDictMemberModifiers(m, t) => {
                if m.required {
                    required = true;
                }
                if m.not_required {
                    required = false;
                }
                read_only |= m.read_only;
                t
            }
            _ => self.as_type(calculated, NodeRef::new(self.file, expr.index())),
        };
        TypedDictMember {
            name,
            type_,
            required,
            read_only,
        }
    }

    pub(super) fn compute_type_get_item_on_typed_dict_field_modifier(
        &mut self,
        slice_type: SliceType,
        modifier: TypedDictFieldModifier,
    ) -> TypeContent<'static, 'static> {
        let mut iterator = slice_type.iter();
        let first = iterator.next().unwrap();
        if let Some(next) = iterator.next() {
            let name = modifier.name();
            self.add_issue(next.as_node_ref(), IssueKind::MustHaveOneArgument { name });
            TypeContent::Unknown(UnknownCause::ReportedIssue)
        } else {
            let mut modifiers = TypedDictFieldModifiers::default();
            let t = match self.compute_slice_type_content(first).remove_annotated() {
                TypeContent::TypedDictMemberModifiers(m, t) => {
                    modifiers = m;
                    t
                }
                tc => self.as_type(tc, first.as_node_ref()),
            };
            let invalid_nested_modifier = |modifier: &'static str| {
                self.add_issue(
                    first.as_node_ref(),
                    IssueKind::TypedDictFieldModifierCannotBeNested { modifier },
                );
            };
            match modifier {
                TypedDictFieldModifier::Required => {
                    if modifiers.required {
                        invalid_nested_modifier("Required")
                    } else if modifiers.not_required {
                        invalid_nested_modifier("NotRequired")
                    } else {
                        modifiers.required = true;
                    }
                }
                TypedDictFieldModifier::NotRequired => {
                    if modifiers.required {
                        invalid_nested_modifier("Required")
                    } else if modifiers.not_required {
                        invalid_nested_modifier("NotRequired")
                    } else {
                        modifiers.not_required = true;
                    }
                }
                TypedDictFieldModifier::ReadOnly => {
                    if modifiers.read_only {
                        invalid_nested_modifier("ReadOnly")
                    }
                    modifiers.read_only = true;
                }
            };
            TypeContent::TypedDictMemberModifiers(modifiers, t)
        }
    }

    pub(super) fn compute_type_get_item_on_typed_dict(
        &mut self,
        typed_dict: Arc<TypedDict>,
        slice_type: SliceType,
    ) -> TypeContent<'db, 'db> {
        let db = self.i_s.db;
        let mut generics = vec![];
        let type_var_likes = match &typed_dict.generics {
            TypedDictGenerics::NotDefinedYet(type_var_likes) => type_var_likes,
            _ => &db.python_state.empty_type_var_likes,
        };
        self.calculate_type_arguments(
            slice_type,
            &mut generics,
            slice_type.iter(),
            type_var_likes,
            &|| {
                typed_dict
                    .name_or_fallback(&FormatData::new_short(db))
                    .into()
            },
            |slf: &mut Self, counts| {
                slf.add_issue(
                    slice_type.as_node_ref(),
                    IssueKind::TypeArgumentIssue {
                        class: typed_dict
                            .name_or_fallback(&FormatData::new_short(slf.i_s.db))
                            .into(),
                        counts,
                    },
                );
            },
        );
        let generics = match generics.is_empty() {
            true => TypedDictGenerics::None,
            false => TypedDictGenerics::Generics(GenericsList::generics_from_vec(generics)),
        };
        if type_var_likes.is_empty() {
            // Issue should have been added previously, because we calculated the type_var_likes
            TypeContent::Type(Type::TypedDict(typed_dict))
        } else {
            let new_td = typed_dict.apply_generics(db, generics);
            TypeContent::Type(Type::TypedDict(new_td))
        }
    }
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_class_typed_dict_member(
        &self,
        name: StringSlice,
        annotation: Annotation,
        total: bool,
    ) -> TypedDictMember {
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            NodeRef::new(self.file, annotation.index()).as_link(),
            &mut x,
            TypeComputationOrigin::TypedDictMember,
        );

        let mut member = comp.compute_typed_dict_member(name, annotation.expression(), total);
        let type_vars = comp.into_type_vars(|_, recalculate_type_vars| {
            member.type_ = recalculate_type_vars(&member.type_);
        });
        debug_assert!(type_vars.is_empty());
        member
    }
}

pub(super) fn new_typed_dict_with_execution_syntax<'db>(
    i_s: &InferenceState<'db, '_>,
    comp: &mut TypeComputation,
    args: &dyn Args<'db>,
) -> Option<(StringSlice, Box<[TypedDictMember]>, bool)> {
    let mut iterator = args.iter(i_s.mode);
    let Some(first_arg) = iterator.next() else {
        args.add_issue(i_s, IssueKind::TypedDictFirstArgMustBeString);
        return None;
    };
    let ArgKind::Positional(first) = first_arg.kind else {
        args.add_issue(i_s, IssueKind::UnexpectedArgumentsToTypedDict);
        return None;
    };
    let expr = first.node_ref.expect_named_expression().expression();
    let Some(name) = StringSlice::from_string_in_expression(first.node_ref.file_index(), expr)
    else {
        first
            .node_ref
            .add_issue(i_s, IssueKind::TypedDictFirstArgMustBeString);
        return None;
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
                IssueKind::TypedDictNameMismatch {
                    string_name: Box::from(name),
                    variable_name: Box::from(definition_name.as_code()),
                },
            );
        }
    } else {
        recoverable_error!("Shouldn only ever get a normal TypedDict initialization for aliases");
        return None;
    }

    let Some(second_arg) = iterator.next() else {
        args.add_issue(i_s, IssueKind::TooFewArguments(" for TypedDict()".into()));
        return None;
    };
    let ArgKind::Positional(second) = second_arg.kind else {
        second_arg.add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
        return None;
    };
    let Some(atom_content) = second
        .node_ref
        .expect_named_expression()
        .expression()
        .maybe_unpacked_atom()
    else {
        second
            .node_ref
            .add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
        return None;
    };
    let mut total = true;
    if let Some(next) = iterator.next() {
        match &next.kind {
            ArgKind::Keyword(kw) if kw.key == "total" => {
                total = check_typed_dict_total_argument(kw.expression, |issue| {
                    next.add_issue(i_s, issue)
                })?;
            }
            ArgKind::Keyword(kw) => {
                let s = format!(
                    r#"Unexpected keyword argument "{}" for "TypedDict""#,
                    kw.key
                );
                kw.add_issue(i_s, IssueKind::ArgumentIssue(s.into()));
                return None;
            }
            _ => {
                args.add_issue(i_s, IssueKind::UnexpectedArgumentsToTypedDict);
                return None;
            }
        };
    }
    if iterator.next().is_some() {
        args.add_issue(i_s, IssueKind::TooManyArguments(" for \"TODO()\"".into()));
        return None;
    }
    let dct_iterator = match atom_content {
        AtomContent::Dict(dct) => dct.iter_elements(),
        _ => {
            second
                .node_ref
                .add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
            return None;
        }
    };
    let mut members = TypedDictMemberGatherer::default();
    for element in dct_iterator {
        match element {
            DictElement::KeyValue(key_value) => {
                let Some(name) = StringSlice::from_string_in_expression(
                    first.node_ref.file_index(),
                    key_value.key(),
                ) else {
                    NodeRef::new(first.node_ref.file, key_value.key().index())
                        .add_issue(i_s, IssueKind::TypedDictInvalidFieldName);
                    return None;
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
                    .add_issue(i_s, IssueKind::TypedDictInvalidFieldName);
                return None;
            }
        };
    }
    Some((name, members.into_boxed_slice(), total))
}

pub(super) fn check_typed_dict_total_argument(
    expr: Expression,
    add_issue: impl Fn(IssueKind),
) -> Option<bool> {
    let result = expr.maybe_simple_bool();
    if result.is_none() {
        add_issue(IssueKind::ArgumentMustBeTrueOrFalse {
            key: "total".into(),
        });
    }
    result
}

#[derive(Default)]
pub(super) struct TypedDictMemberGatherer {
    members: Vec<TypedDictMember>,
    first_after_merge_index: usize,
}

impl TypedDictMemberGatherer {
    pub(crate) fn add(&mut self, db: &Database, member: TypedDictMember) -> Result<(), IssueKind> {
        let key = member.name.as_str(db);
        if let Some((i, m)) = self
            .members
            .iter_mut()
            .enumerate()
            .find(|(_, m)| m.name.as_str(db) == key)
        {
            if i >= self.first_after_merge_index {
                Err(IssueKind::TypedDictDuplicateKey { key: key.into() })
            } else {
                *m = member;
                Err(IssueKind::TypedDictOverwritingKeyWhileExtending { key: key.into() })
            }
        } else {
            self.members.push(member);
            Ok(())
        }
    }

    pub fn merge(&mut self, db: &Database, node_ref: NodeRef, slice: &[TypedDictMember]) {
        for to_add in slice.iter() {
            let key = to_add.name.as_str(db);
            if let Some(current) = self.members.iter_mut().find(|m| m.name.as_str(db) == key) {
                node_ref.add_type_issue(
                    db,
                    IssueKind::TypedDictOverwritingKeyWhileMerging { key: key.into() },
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
