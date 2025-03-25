// For Type Application, e.g. x = list[int]()
use std::rc::Rc;

use super::super::name_resolution::NameResolution;
use super::{TypeComputation, TypeComputationOrigin, TypeContent, TypeVarCallbackReturn};
use crate::matching::ResultContext;
use crate::{
    database::{ComplexPoint, Specific, TypeAlias},
    diagnostics::IssueKind,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{Dataclass, NamedTuple, Type, TypeVarLike, TypedDict},
    type_helpers::Class,
};

macro_rules! compute_type_application {
    ($self:ident, $slice_type:expr, $result_context:expr, $method:ident $args:tt) => {{
        let from_alias_definition = match $result_context {
            ResultContext::AssignmentNewDefinition { assignment_definition } => {
                let node_ref = NodeRef::from_link($self.i_s.db, *assignment_definition);
                let assignment = node_ref.expect_assignment();
                return $self.compute_explicit_type_assignment(assignment);
            }
            _ => false,
        };
        let mut on_type_var = |i_s: &InferenceState, _: &_, type_var_like: TypeVarLike, current_callable: Option<_>| {
            if let Some(result) = i_s.find_parent_type_var(&type_var_like) {
                return result
            }
            if from_alias_definition || current_callable.is_some(){
                TypeVarCallbackReturn::NotFound { allow_late_bound_callables: !from_alias_definition }
            } else {
                TypeVarCallbackReturn::UnboundTypeVar
            }
        };
        let mut tcomp = TypeComputation::new(
            $self.i_s,
            $self.file,
            $slice_type.as_node_ref().as_link(),
            &mut on_type_var,
            match from_alias_definition {
                false => TypeComputationOrigin::TypeApplication,
                true => TypeComputationOrigin::TypeAlias,
            }
        );
        let t = tcomp.$method $args;
        match t {
            TypeContent::SimpleGeneric{class_link, generics, ..} => {
                Inferred::from_type(Type::Type(Rc::new(Type::new_class(class_link, generics))))
            }
            TypeContent::Type(mut type_) => {
                let type_var_likes = tcomp.into_type_vars(|_, recalculate_type_vars| {
                    type_ = recalculate_type_vars(&type_);
                });
                if type_var_likes.len() > 0 && from_alias_definition  {
                    debug_assert!(from_alias_definition);
                    Inferred::new_unsaved_complex(ComplexPoint::TypeAlias(Box::new(TypeAlias::new_valid(
                        type_var_likes,
                        $slice_type.as_node_ref().as_link(),
                        None,
                        Rc::new(type_),
                        false,
                    ))))
                } else {
                    Inferred::from_type(Type::Type(Rc::new(type_)))
                }
            },
            TypeContent::Unknown(cause) => Inferred::new_any(cause.into()),
            TypeContent::InvalidVariable(var) => {
                var.add_issue(
                    $self.i_s.db,
                    |issue| $slice_type.as_node_ref().add_issue($self.i_s, issue),
                    tcomp.origin
                );
                Inferred::new_any_from_error()
            }
            _ => {
                // Currently this is only the case with Annotated. Not sure if this is correct in
                // the future, but for now returning typing._SpecialForm seems fine.
                Inferred::from_type($self.i_s.db.python_state.typing_special_form_type())
            }
        }
    }}
}

impl<'db, 'file> NameResolution<'db, 'file, '_> {
    pub(crate) fn compute_type_application_on_class(
        &self,
        class: Class,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            result_context,
            compute_type_get_item_on_class(class, slice_type, None)
        )
    }

    pub(crate) fn compute_type_application_on_dataclass(
        &self,
        dataclass: &Dataclass,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            result_context,
            compute_type_get_item_on_dataclass(dataclass, slice_type, None)
        )
    }

    pub(crate) fn compute_type_application_on_named_tuple(
        &self,
        named_tuple: Rc<NamedTuple>,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            result_context,
            compute_type_get_item_on_named_tuple(named_tuple, slice_type)
        )
    }

    pub(crate) fn compute_type_application_on_typed_dict(
        &self,
        typed_dict: &TypedDict,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        compute_type_application!(
            self,
            slice_type,
            result_context,
            compute_type_get_item_on_typed_dict(typed_dict, slice_type)
        )
    }

    pub(crate) fn compute_type_application_on_alias(
        &self,
        alias: &TypeAlias,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        let from_alias_definition = matches!(
            result_context,
            ResultContext::AssignmentNewDefinition { .. }
        );
        if !from_alias_definition && !alias.application_allowed() {
            slice_type
                .as_node_ref()
                .add_issue(self.i_s, IssueKind::OnlyClassTypeApplication);
            return Inferred::new_any_from_error();
        }
        compute_type_application!(
            self,
            slice_type,
            result_context,
            compute_type_get_item_on_alias(alias, slice_type)
        )
    }

    pub(crate) fn compute_type_application_on_typing_class(
        &self,
        specific: Specific,
        slice_type: SliceType,
        result_context: &ResultContext,
    ) -> Inferred {
        match specific {
            Specific::TypingGeneric | Specific::TypingProtocol => {
                self.add_issue(
                    slice_type.cst_node.index(),
                    IssueKind::InvalidType("Invalid type application".to_string().into()),
                );
                Inferred::new_any_from_error()
            }
            Specific::TypingTuple => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_type_get_item_on_tuple(slice_type)
                )
            }
            Specific::TypingCallable => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_type_get_item_on_callable(slice_type)
                )
            }
            Specific::TypingUnion => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_type_get_item_on_union(slice_type)
                )
            }
            Specific::TypingOptional => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_type_get_item_on_optional(slice_type)
                )
            }
            Specific::TypingType | Specific::BuiltinsType => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_type_get_item_on_type(slice_type)
                )
            }
            Specific::TypingLiteral => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_get_item_on_literal(slice_type)
                )
            }
            Specific::TypingAnnotated => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_get_item_on_annotated(slice_type)
                )
            }
            Specific::MypyExtensionsFlexibleAlias => {
                compute_type_application!(
                    self,
                    slice_type,
                    result_context,
                    compute_get_item_on_flexible_alias(slice_type)
                )
            }
            _ => unreachable!("{:?}", specific),
        }
    }
}
