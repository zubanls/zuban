use std::{borrow::Cow, cell::Cell};

use parsa_python_cst::{
    FunctionDef, FunctionParent, Name, NodeIndex, ParamAnnotation, ParamKind, ReturnAnnotation,
    ReturnOrYield,
};
use utils::FastHashSet;

use crate::{
    database::{ComplexPoint, Database, Locality, ParentScope, Point, PointLink, Specific},
    diagnostics::{Issue, IssueKind},
    file::{FUNC_TO_RETURN_OR_YIELD_DIFF, FUNC_TO_TYPE_VAR_DIFF, PythonFile, func_parent_scope},
    inference_state::InferenceState,
    new_class,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        AnyCause, StringSlice, Type, TypeGuardInfo, TypeVarKind, TypeVarLike, TypeVarLikes,
        TypeVarManager,
    },
    type_helpers::{Class, Function},
};

use super::{
    ClassNodeRef, TypeComputation, TypeComputationOrigin, TypeVarCallbackReturn,
    use_cached_param_annotation_type,
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct FuncNodeRef<'file>(NodeRef<'file>);

impl<'a> std::ops::Deref for FuncNodeRef<'a> {
    type Target = NodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::cmp::PartialEq<NodeRef<'_>> for FuncNodeRef<'_> {
    fn eq(&self, other: &NodeRef) -> bool {
        self.0 == *other
    }
}

impl<'a> From<FuncNodeRef<'a>> for NodeRef<'a> {
    fn from(value: FuncNodeRef<'a>) -> Self {
        value.0
    }
}

impl<'db: 'file, 'file> FuncNodeRef<'file> {
    #[inline]
    pub fn new(file: &'file PythonFile, node_index: NodeIndex) -> Self {
        Self::from_node_ref(NodeRef::new(file, node_index))
    }

    #[inline]
    pub fn from_node_ref(node_ref: NodeRef<'file>) -> Self {
        debug_assert!(node_ref.maybe_function().is_some(), "{node_ref:?}");
        Self(node_ref)
    }

    pub fn node(&self) -> FunctionDef<'file> {
        FunctionDef::by_index(&self.file.tree, self.node_index)
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation<'_>> {
        self.node().return_annotation()
    }

    pub fn expect_return_annotation_node_ref(&self) -> NodeRef<'_> {
        NodeRef::new(
            self.file,
            self.return_annotation().unwrap().expression().index(),
        )
    }

    pub fn is_typed(&self) -> bool {
        self.node().is_typed()
    }

    pub fn iter_return_or_yield(&self) -> ReturnOrYieldIterator<'file> {
        let def_point = self
            .file
            .points
            .get(self.node_index + FUNC_TO_RETURN_OR_YIELD_DIFF);
        let first_return_or_yield = def_point.node_index();
        ReturnOrYieldIterator {
            file: self.file,
            next_node_index: first_return_or_yield,
        }
    }

    pub fn is_generator(&self) -> bool {
        for return_or_yield in self.iter_return_or_yield() {
            if let ReturnOrYield::Yield(_) = return_or_yield {
                return true;
            }
        }
        false
    }

    pub fn is_async(&self) -> bool {
        matches!(
            self.node().parent(),
            FunctionParent::Async | FunctionParent::DecoratedAsync(_)
        )
    }

    pub fn type_vars(&self, db: &'db Database) -> &'file TypeVarLikes {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            TypeVarLikes::load_saved_type_vars(db, type_var_reference)
        } else {
            recoverable_error!("Function type vars accessed, but they are not yet calculated");
            &db.python_state.empty_type_var_likes
        }
    }

    fn type_var_reference(&self) -> NodeRef<'file> {
        self.add_to_node_index(FUNC_TO_TYPE_VAR_DIFF)
    }

    pub fn unannotated_return_reference(&self) -> NodeRef<'file> {
        NodeRef::new(self.file, self.node().colon_index())
    }

    pub(crate) fn add_issue_for_declaration(&self, i_s: &InferenceState, kind: IssueKind) -> bool {
        let node = self.node();
        self.file.maybe_add_issue(
            i_s,
            Issue::from_start_stop(node.start(), node.end_position_of_colon(), kind),
        )
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) -> bool {
        let node = self.node();
        if let Some(decorated) = node.maybe_decorated() {
            self.file.maybe_add_issue(
                i_s,
                Issue::from_start_stop(decorated.start(), decorated.end_position_last_leaf(), kind),
            )
        } else {
            self.add_issue_for_declaration(i_s, kind)
        }
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.file_index(), name.start(), name.end())
    }

    pub fn name(&self) -> &'file str {
        let func = FunctionDef::by_index(&self.file.tree, self.node_index);
        func.name().as_str()
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let base = match self.parent(db) {
            FuncParent::Module | FuncParent::Function(_) => self.file.qualified_name(db),
            FuncParent::Class(c) => c.qualified_name(db),
        };
        format!("{base}.{}", self.name())
    }

    pub fn parent_scope(&self) -> ParentScope {
        func_parent_scope(&self.file.tree, &self.file.points, self.node_index)
    }

    pub(crate) fn parent(&self, db: &'db Database) -> FuncParent<'db> {
        match self.parent_scope() {
            ParentScope::Module => FuncParent::Module,
            ParentScope::Class(class_index) => {
                let n = ClassNodeRef::new(self.file, class_index).to_db_lifetime(db);
                FuncParent::Class(Class::with_self_generics(db, n))
            }
            ParentScope::Function(func_index) => {
                let n = NodeRef::new(self.file, func_index).to_db_lifetime(db);
                FuncParent::Function(Function::new_with_unknown_parent(db, n))
            }
        }
    }

    pub(crate) fn ensure_cached_type_vars(
        &self,
        i_s: &InferenceState<'db, '_>,
        class: Option<ClassNodeRef>,
    ) -> Option<(Option<TypeGuardInfo>, Option<ParamAnnotation<'_>>)> {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            return None; // TODO this feels wrong, because below we only sometimes calculate the callable
        }
        let node = self.node();
        let is_staticmethod = class.is_some()
            && node.maybe_decorated().is_some_and(|decorated| {
                decorated.decorators().iter().any(|decorator| {
                    // TODO this is not proper type inference, but should probably
                    // suffice for now.
                    decorator.as_code().contains("staticmethod")
                })
            });
        let (mut type_vars, type_guard, star_annotation) =
            self.cache_type_vars(i_s, class, is_staticmethod);
        if type_vars.is_empty() && i_s.db.project.should_infer_untyped_params() {
            if !node.is_typed() && !["__init__", "__new__"].contains(&node.name().as_code()) {
                let mut skip_first = class.is_some();
                if skip_first && is_staticmethod {
                    skip_first = false;
                }
                type_vars = TypeVarLikes::new_untyped_params(node, skip_first)
            }
        }
        match type_vars.is_empty() {
            true => type_var_reference
                .set_point(Point::new_specific(Specific::Analyzed, Locality::Todo)),
            false => type_var_reference
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo),
        }
        debug_assert!(type_var_reference.point().calculated());
        Some((type_guard, star_annotation))
    }

    fn cache_type_vars(
        &self,
        i_s: &InferenceState<'db, '_>,
        class: Option<ClassNodeRef<'_>>,
        is_staticmethod: bool,
    ) -> (
        TypeVarLikes,
        Option<TypeGuardInfo>,
        Option<ParamAnnotation<'_>>,
    ) {
        let func_node = self.node();
        let type_params = func_node.type_params();
        let mut known_type_vars = None;
        if let Some(type_params) = type_params {
            known_type_vars = Some(
                self.file
                    .name_resolution_for_types(i_s)
                    .compute_type_params_definition(i_s.as_parent_scope(), type_params, true),
            );
        }
        let implicit_optional = self.file.flags(i_s.db).implicit_optional;
        let in_result_type = Cell::new(false);
        let mut unbound_in_params = vec![];
        #[allow(clippy::mutable_key_type)]
        let mut unbound_type_vars = FastHashSet::default();
        #[allow(clippy::mutable_key_type)]
        let mut unbound_param_specs: FastHashSet<TypeVarLike> = FastHashSet::default();
        let mut on_type_var = |i_s: &InferenceState,
                               manager: &TypeVarManager<PointLink>,
                               type_var_like: TypeVarLike,
                               current_callable: Option<_>,
                               on_name: Name| {
            class
                .and_then(|class| {
                    class
                        .use_cached_type_vars(i_s.db)
                        .find(&type_var_like, class.as_link())
                        .map(TypeVarCallbackReturn::TypeVarLike)
                })
                .or_else(|| i_s.find_parent_type_var(&type_var_like))
                .unwrap_or_else(|| {
                    if let Some(known_type_vars) = &known_type_vars {
                        if known_type_vars
                            .find(&type_var_like, self.as_link())
                            .is_some()
                        {
                            return TypeVarCallbackReturn::NotFound {
                                allow_late_bound_callables: in_result_type.get(),
                            };
                        }
                        unbound_type_vars.insert(type_var_like);
                        return TypeVarCallbackReturn::AnyDueToError;
                    }
                    if in_result_type.get() {
                        if manager.position(&type_var_like).is_none() && current_callable.is_none()
                        {
                            unbound_in_params.push(type_var_like.clone());
                        } else if let TypeVarLike::ParamSpec(_) = &type_var_like {
                            unbound_param_specs.remove(&type_var_like);
                        }
                    } else if let TypeVarLike::ParamSpec(_) = &type_var_like
                        && manager.position(&type_var_like).is_none()
                        && on_name.is_part_of_primary_ancestors()
                    {
                        unbound_param_specs.insert(type_var_like);
                    }
                    TypeVarCallbackReturn::NotFound {
                        allow_late_bound_callables: in_result_type.get(),
                    }
                })
        };
        let mut type_computation = TypeComputation::new(
            i_s,
            self.file,
            self.as_link(),
            &mut on_type_var,
            TypeComputationOrigin::ParamTypeCommentOrAnnotation { is_staticmethod },
        );
        let mut star_annotation = None;
        let mut previous_param = None;
        let mut method_self_non_self_bound = false;
        for (i, param) in func_node.params().iter().enumerate() {
            if let Some(annotation) = param.annotation() {
                let mut is_implicit_optional = false;
                if implicit_optional
                    && let Some(default) = param.default()
                    && default.as_code() == "None"
                {
                    is_implicit_optional = true;
                }
                let param_kind = param.kind();
                type_computation.cache_param_annotation(
                    annotation,
                    param_kind,
                    previous_param,
                    is_implicit_optional,
                );
                if param_kind == ParamKind::Star {
                    star_annotation = Some(annotation);
                }
                if i == 0
                    && class.is_some()
                    && !is_staticmethod
                    && !type_computation
                        .use_cached_param_annotation_type(annotation)
                        .has_self_type(i_s.db)
                {
                    method_self_non_self_bound = true;
                }
            }
            previous_param = Some(param);
        }
        if let Some(annotation) = star_annotation {
            let t = use_cached_param_annotation_type(i_s.db, self.file, annotation);
            if let Type::ParamSpecArgs(usage) = t.as_ref() {
                let iterator = func_node.params().iter();
                // The type computation only checked if **kwargs was ok. If there is no param, no
                // issue was added, so add it here.
                if !iterator
                    .skip_while(|p| p.kind() != ParamKind::Star)
                    .nth(1)
                    .is_some_and(|p| p.annotation().is_some())
                {
                    NodeRef::new(self.file, annotation.index()).add_issue(
                        i_s,
                        IssueKind::ParamSpecParamsNeedBothStarAndStarStar {
                            name: usage.param_spec.name(i_s.db).into(),
                        },
                    );
                }
            }
        }
        let type_guard = func_node.return_annotation().and_then(|return_annot| {
            in_result_type.set(true);
            let result = type_computation.cache_return_annotation(return_annot);
            if method_self_non_self_bound
                && type_computation
                    .use_cached_return_annotation_type(return_annot)
                    .has_self_type(i_s.db)
            {
                self.expect_return_annotation_node_ref()
                    .add_type_issue(i_s.db, IssueKind::SelfArgumentMissing);
            }
            result
        });
        // Here we recompute the TypeVars, even if they are already known because of TypeParams.
        // This is a bit weird, but it's needed, because otherwise we don't have the late bound
        // calculation that is needed for:
        //
        //     def decorator2[**P, R](x: int) -> Callable[[Callable[P, R]], Callable[P, R]]
        //
        // This is part of the conformance tests and behaves there like normal late bound callables
        // do.
        let type_vars = type_computation.into_type_vars(|inf, recalculate_type_vars| {
            for param in func_node.params().iter() {
                if let Some(annotation) = param.annotation() {
                    inf.recalculate_annotation_type_vars(annotation.index(), recalculate_type_vars);
                }
            }
            if let Some(return_annot) = func_node.return_annotation() {
                inf.recalculate_annotation_type_vars(return_annot.index(), recalculate_type_vars);
            }
        });
        if !unbound_in_params.is_empty()
            && let Type::TypeVar(usage) = self.return_type(i_s).as_ref()
            && unbound_in_params.contains(&TypeVarLike::TypeVar(usage.type_var.clone()))
        {
            let node_ref = self.expect_return_annotation_node_ref();
            let note = if let TypeVarKind::Bound(bound) = usage.type_var.kind(i_s.db) {
                Some(
                    format!(
                        "Consider using the upper bound \"{}\" instead",
                        bound.format_short(i_s.db)
                    )
                    .into(),
                )
            } else {
                None
            };
            node_ref.add_issue(i_s, IssueKind::TypeVarInReturnButNotArgument { note });
        }
        for type_var_like in unbound_type_vars.into_iter() {
            self.add_issue_for_declaration(
                i_s,
                IssueKind::TypeParametersShouldBeDeclared { type_var_like },
            );
        }
        for type_var_like in unbound_param_specs.into_iter() {
            self.add_issue_for_declaration(i_s, IssueKind::UnboundTypeVarLike { type_var_like });
        }
        (type_vars, type_guard, star_annotation)
    }

    pub fn return_annotation_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'file, Type> {
        self.return_annotation()
            .map(|a| {
                self.file
                    .name_resolution_for_types(i_s)
                    .use_cached_return_annotation_type(a)
            })
            .unwrap_or_else(|| Cow::Borrowed(&Type::Any(AnyCause::Unannotated)))
    }

    pub fn return_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'file, Type> {
        let t = self.return_annotation_type(i_s);
        if self.is_async() && !self.is_generator() {
            Cow::Owned(new_class!(
                i_s.db.python_state.coroutine_link(),
                Type::Any(AnyCause::Todo),
                Type::Any(AnyCause::Todo),
                t.into_owned(),
            ))
        } else {
            t
        }
    }
}

pub(crate) struct ReturnOrYieldIterator<'a> {
    file: &'a PythonFile,
    next_node_index: NodeIndex,
}

impl<'a> Iterator for ReturnOrYieldIterator<'a> {
    type Item = ReturnOrYield<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next_node_index == 0 {
            None
        } else {
            let point = self.file.points.get(self.next_node_index);
            let index = self.next_node_index;
            self.next_node_index = point.node_index();
            // - 1 because the index points to the next yield/return literal. The parent of those
            // literals are then `return_stmt` and `yield_expr` terminals.
            Some(ReturnOrYield::by_index(&self.file.tree, index - 1))
        }
    }
}

pub(crate) enum FuncParent<'x> {
    Module,
    Function(Function<'x, 'x>),
    Class(Class<'x>),
}
