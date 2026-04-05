use std::sync::Arc;

use parsa_python_cst::{
    Annotation, ArgsIterator, Argument, ArgumentsDetails, AtomContent, DictElement, Expression,
    Name,
};

use crate::{
    arguments::Args,
    database::{Database, TypedDictArgs},
    diagnostics::IssueKind,
    file::{PythonFile, name_resolution::NameResolution},
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        ExtraItemsType, GenericsList, NeverCause, StringSlice, Type, TypedDict, TypedDictGenerics,
        TypedDictMember, TypedDictMembers,
    },
};

use super::{
    TypeComputation, TypeComputationOrigin, TypeContent, TypedDictFieldModifier,
    TypedDictFieldModifiers, UnknownCause, type_computation_for_variable_annotation,
};

struct TypedDictMemberType {
    pub type_: Type,
    pub required: Option<bool>,
    pub read_only: bool,
}

impl<'db: 'file, 'file, 'i_s, 'c> TypeComputation<'db, 'file, 'i_s, 'c> {
    fn compute_typed_dict_member(
        &mut self,
        initialization_args: &TypedDictArgs,
        name: StringSlice,
        expr: Expression,
    ) -> TypedDictMember {
        let tt = self.compute_typed_dict_type(expr);
        TypedDictMember {
            name,
            type_: tt.type_,
            required: tt
                .required
                .unwrap_or_else(|| initialization_args.total.unwrap_or(true)),
            read_only: tt.read_only,
        }
    }

    fn compute_typed_dict_type(&mut self, expr: Expression) -> TypedDictMemberType {
        let calculated = self.compute_type(expr).remove_annotated();
        let mut required = None;
        let mut read_only = false;
        let type_ = match calculated {
            TypeContent::TypedDictMemberModifiers(m, t) => {
                if m.required {
                    required = Some(true);
                }
                if m.not_required {
                    required = Some(false);
                }
                read_only |= m.read_only;
                t
            }
            _ => self.as_type(calculated, NodeRef::new(self.file, expr.index())),
        };
        TypedDictMemberType {
            type_,
            required,
            read_only,
        }
    }

    fn compute_functional_typed_dict_extra_items(
        &mut self,
        initialization_args: &TypedDictArgs,
    ) -> Option<ExtraItemsType> {
        initialization_args.calc_extra_items_type(self.i_s.db, self.file, |expr| {
            self.compute_typed_dict_type(expr)
        })
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
            typed_dict.name.unwrap_or_else(|| {
                recoverable_error!(
                    "Get item should only be possible for a TypedDict type computation"
                );
                NodeRef::from_link(db, typed_dict.defined_at).string_slice()
            }),
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
        initialization_args: &TypedDictArgs,
        name: StringSlice,
        annotation: Annotation,
    ) -> TypedDictMember {
        let t = self.compute_class_typed_dict_type(annotation.expression());
        TypedDictMember {
            name,
            type_: t.type_,
            required: t
                .required
                .unwrap_or_else(|| initialization_args.total.unwrap_or(true)),
            read_only: t.read_only,
        }
    }

    fn compute_class_typed_dict_type(&self, expr: Expression) -> TypedDictMemberType {
        let mut x = type_computation_for_variable_annotation;
        let mut comp = TypeComputation::new(
            self.i_s,
            self.file,
            NodeRef::new(self.file, expr.index()).as_link(),
            &mut x,
            TypeComputationOrigin::TypedDictMember,
        );

        let mut t = comp.compute_typed_dict_type(expr);
        let type_vars = comp.into_type_vars(|_, recalculate_type_vars| {
            t.type_ = recalculate_type_vars(&t.type_);
        });
        debug_assert!(type_vars.is_empty());
        t
    }

    pub fn compute_class_typed_dict_extra_items(
        &self,
        initialization_args: &TypedDictArgs,
    ) -> Option<ExtraItemsType> {
        initialization_args.calc_extra_items_type(self.i_s.db, self.file, |expr| {
            self.compute_class_typed_dict_type(expr)
        })
    }
}

impl TypedDictArgs {
    fn calc_extra_items_type(
        &self,
        db: &Database,
        file: &PythonFile,
        callback: impl FnOnce(Expression) -> TypedDictMemberType,
    ) -> Option<ExtraItemsType> {
        let mut result = None;
        if let Some(expr_index) = self.extra_items {
            let expr = NodeRef::new(file, expr_index).expect_expression();
            let t = callback(expr);
            if let Some(required) = t.required {
                NodeRef::new(file, expr_index).add_type_issue(
                    db,
                    IssueKind::TypedDictExtraItemsCannotBe {
                        kind: match required {
                            true => "Required",
                            false => "NotRequired",
                        },
                    },
                );
            }
            result = Some(ExtraItemsType {
                t: t.type_,
                read_only: t.read_only,
            })
        } else if let Some(true) = self.closed {
            result = Some(ExtraItemsType {
                t: Type::Never(NeverCause::Explicit),
                read_only: false,
            })
        }
        result
    }
}

pub(super) fn new_typed_dict_with_execution_syntax<'db>(
    i_s: &InferenceState<'db, '_>,
    comp: &mut TypeComputation,
    args: &dyn Args<'db>,
) -> Option<(StringSlice, TypedDictMembers)> {
    let simple_args = match args.maybe_simple_args().map(|args| args.details) {
        Some(ArgumentsDetails::Node(args)) => args,
        Some(_) => {
            args.add_issue(i_s, IssueKind::TypedDictFirstArgMustBeString);
            return None;
        }
        _ => {
            args.add_issue(i_s, IssueKind::UnexpectedArgumentsToTypedDict);
            return None;
        }
    };
    debug_assert!(args.in_file().is_some());
    let file = args.in_file()?;
    let mut iterator = simple_args.iter();
    let Some(first_arg) = iterator.next() else {
        args.add_issue(i_s, IssueKind::TypedDictFirstArgMustBeString);
        return None;
    };
    let Argument::Positional(first) = first_arg else {
        args.add_issue(i_s, IssueKind::UnexpectedArgumentsToTypedDict);
        return None;
    };
    let expr = first.expression();
    let Some(name) = StringSlice::from_string_in_expression(file.file_index, expr) else {
        NodeRef::new(file, first.index()).add_issue(i_s, IssueKind::TypedDictFirstArgMustBeString);
        return None;
    };

    if let Some(definition_name) = expr
        .maybe_single_string_literal()
        .unwrap()
        .in_simple_assignment()
    {
        let name = name.as_str(i_s.db);
        if name != definition_name.as_code() {
            NodeRef::new(file, first.index()).add_issue(
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
    let Argument::Positional(second) = second_arg else {
        NodeRef::new(file, second_arg.index())
            .add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
        return None;
    };
    let Some(atom_content) = second.expression().maybe_unpacked_atom() else {
        NodeRef::new(file, second.index()).add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
        return None;
    };
    let options = check_typed_dict_arguments(i_s, file, iterator, false, |issue| {
        args.add_issue(i_s, issue)
    });
    let dct_iterator = match atom_content {
        AtomContent::Dict(dct) => dct.iter_elements(),
        _ => {
            NodeRef::new(file, second.index())
                .add_issue(i_s, IssueKind::TypedDictSecondArgMustBeDict);
            return None;
        }
    };
    let mut members = TypedDictMemberGatherer::default();
    for element in dct_iterator {
        match element {
            DictElement::KeyValue(key_value) => {
                let Some(name) =
                    StringSlice::from_string_in_expression(file.file_index, key_value.key())
                else {
                    NodeRef::new(file, key_value.key().index())
                        .add_issue(i_s, IssueKind::TypedDictInvalidFieldName);
                    return None;
                };
                if let Err(issue) = members.add(
                    i_s,
                    comp.compute_typed_dict_member(&options, name, key_value.value()),
                    None,
                ) {
                    NodeRef::new(file, key_value.key().index()).add_issue(i_s, issue);
                }
                key_value.key();
            }
            DictElement::Star(d) => {
                NodeRef::new(file, d.index()).add_issue(i_s, IssueKind::TypedDictInvalidFieldName);
                return None;
            }
        };
    }
    Some((
        name,
        TypedDictMembers {
            named: members.into_boxed_slice(),
            extra_items: comp.compute_functional_typed_dict_extra_items(&options),
        },
    ))
}

pub(super) fn check_typed_dict_arguments<'file>(
    i_s: &InferenceState,
    file: &PythonFile,
    args: ArgsIterator<'file>,
    ignore_positional: bool,
    add_issue: impl Fn(IssueKind) -> bool,
) -> TypedDictArgs {
    let mut result = TypedDictArgs::default();

    let check_bool = |name: Name, expr: Expression| {
        let result = expr.maybe_simple_bool();
        if result.is_none() {
            add_issue(IssueKind::ArgumentMustBeTrueOrFalse {
                key: name.as_code().into(),
            });
        }
        result
    };
    for argument in args {
        match argument {
            Argument::Keyword(kw) => {
                let (name, expr) = kw.unpack();
                match name.as_code() {
                    "total" => {
                        result.total = check_bool(name, expr);
                    }
                    "extra_items" => result.extra_items = Some(expr.index()),
                    "closed" => {
                        result.closed = check_bool(name, expr);
                    }
                    name => {
                        let s =
                            format!(r#"Unexpected keyword argument "{}" for "TypedDict""#, name);
                        NodeRef::new(file, kw.index())
                            .add_issue(i_s, IssueKind::ArgumentIssue(s.into()));
                    }
                }
            }
            Argument::Positional(_) if ignore_positional => continue,
            _ => {
                add_issue(IssueKind::UnexpectedArgumentsToTypedDict);
            }
        }
    }
    result
}

#[derive(Default)]
pub(super) struct TypedDictMemberGatherer {
    members: Vec<TypedDictMember>,
    first_after_merge_index: usize,
}

impl TypedDictMemberGatherer {
    pub(crate) fn add(
        &mut self,
        i_s: &InferenceState,
        member: TypedDictMember,
        base_class_extra_type: Option<&ExtraItemsType>,
    ) -> Result<(), IssueKind> {
        let key = member.name.as_str(i_s.db);
        if let Some((i, m)) = self
            .members
            .iter_mut()
            .enumerate()
            .find(|(_, m)| m.name.as_str(i_s.db) == key)
        {
            if i >= self.first_after_merge_index {
                Err(IssueKind::TypedDictDuplicateKey { key: key.into() })
            } else {
                let result = if m.read_only
                    && !(m.required && !member.required)
                    && m.type_.is_simple_super_type_of(i_s, &member.type_).bool()
                {
                    // Allow read-only overwrites with subtypes
                    Ok(())
                } else {
                    Err(IssueKind::TypedDictOverwritingKeyWhileExtending { key: key.into() })
                };
                *m = member;
                result
            }
        } else {
            let mut result = Ok(());
            if let Some(extra) = base_class_extra_type {
                if member.required && !extra.read_only {
                    result = Err(IssueKind::TypedDictMemberRequiredButHasExtraItemsOfSuper {
                        name: member.name.as_str(i_s.db).into(),
                    });
                } else if !extra.read_only && member.read_only {
                    result = Err(
                        IssueKind::TypedDictMemberReadOnlyButExtraItemsOfSuperClassIsNot {
                            name: member.name.as_str(i_s.db).into(),
                        },
                    );
                } else {
                    let matches = if extra.read_only {
                        extra.t.is_simple_super_type_of(i_s, &member.type_)
                    } else {
                        extra.t.is_simple_same_type(i_s, &member.type_)
                    };
                    if !matches.bool() {
                        result = Err(
                            IssueKind::TypedDictMemberNotAssignableToExtraItemsOfSuperClass {
                                name: member.name.as_str(i_s.db).into(),
                                in_super_class: extra.t.format_short(i_s.db),
                                member_type: member.type_.format_short(i_s.db),
                            },
                        );
                    }
                }
            }
            self.members.push(member);
            result
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
