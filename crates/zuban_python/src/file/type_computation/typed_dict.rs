use parsa_python_cst::{Annotation, Expression};

use crate::{
    diagnostics::IssueKind,
    file::name_resolution::NameResolution,
    format_data::FormatData,
    getitem::SliceType,
    node_ref::NodeRef,
    type_::{GenericsList, StringSlice, Type, TypedDict, TypedDictGenerics, TypedDictMember},
};

use super::{
    type_computation_for_variable_annotation, TypeComputation, TypeComputationOrigin, TypeContent,
    TypedDictFieldModifier, TypedDictFieldModifiers, UnknownCause,
};

impl<'db: 'x + 'file, 'file, 'i_s, 'c, 'x> TypeComputation<'db, 'file, 'i_s, 'c> {
    pub fn compute_typed_dict_member(
        &mut self,
        name: StringSlice,
        expr: Expression,
        total: bool,
    ) -> TypedDictMember {
        let calculated = self.compute_type(expr);
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
            let t = match self.compute_slice_type_content(first) {
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
        typed_dict: &TypedDict,
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
                            .name_or_fallback(&FormatData::new_short(db))
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
        let new_td = typed_dict.apply_generics(db, generics);
        TypeContent::Type(Type::TypedDict(new_td))
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
