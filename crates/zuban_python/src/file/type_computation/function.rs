use std::{borrow::Cow, cell::Cell};

use parsa_python_cst::{
    Decorated, FunctionDef, FunctionParent, NodeIndex, ParamAnnotation, ParamKind,
    ReturnAnnotation, ReturnOrYield,
};
use utils::FastHashSet;

use crate::{
    database::{ComplexPoint, Database, Locality, ParentScope, Point, PointLink, Specific},
    diagnostics::{Issue, IssueKind},
    file::{func_parent_scope, PythonFile, FUNC_TO_RETURN_OR_YIELD_DIFF, FUNC_TO_TYPE_VAR_DIFF},
    inference_state::InferenceState,
    node_ref::NodeRef,
    recoverable_error,
    type_::{
        AnyCause, StringSlice, Type, TypeGuardInfo, TypeVarKind, TypeVarLike, TypeVarLikes,
        TypeVarManager,
    },
    type_helpers::{Class, Function},
};

use super::{
    use_cached_param_annotation_type, ClassNodeRef, TypeComputation, TypeComputationOrigin,
    TypeVarCallbackReturn,
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

    pub fn return_annotation(&self) -> Option<ReturnAnnotation> {
        self.node().return_annotation()
    }

    pub fn expect_return_annotation_node_ref(&self) -> NodeRef {
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

    pub(crate) fn expect_decorated_node(&self) -> Decorated {
        self.node().maybe_decorated().unwrap()
    }

    pub(crate) fn add_issue_for_declaration(&self, i_s: &InferenceState, kind: IssueKind) {
        let node = self.node();
        self.file.add_issue(
            i_s,
            Issue {
                kind,
                start_position: node.start(),
                end_position: node.end_position_of_colon(),
            },
        )
    }

    pub(crate) fn add_issue_onto_start_including_decorator(
        &self,
        i_s: &InferenceState,
        kind: IssueKind,
    ) {
        let node = self.node();
        if let Some(decorated) = node.maybe_decorated() {
            NodeRef::new(self.file, decorated.index()).add_issue(i_s, kind)
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
    ) -> Option<(Option<TypeGuardInfo>, Option<ParamAnnotation>)> {
        let type_var_reference = self.type_var_reference();
        if type_var_reference.point().calculated() {
            return None; // TODO this feels wrong, because below we only sometimes calculate the callable
        }
        let (type_vars, type_guard, star_annotation) = self.cache_type_vars(i_s, class);
        match type_vars.len() {
            0 => type_var_reference
                .set_point(Point::new_specific(Specific::Analyzed, Locality::Todo)),
            _ => type_var_reference
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo),
        }
        debug_assert!(type_var_reference.point().calculated());
        Some((type_guard, star_annotation))
    }

    fn cache_type_vars(
        &self,
        i_s: &InferenceState<'db, '_>,
        class: Option<ClassNodeRef>,
    ) -> (TypeVarLikes, Option<TypeGuardInfo>, Option<ParamAnnotation>) {
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
        let mut unbound_type_vars = FastHashSet::default();
        let mut on_type_var = |i_s: &InferenceState,
                               manager: &TypeVarManager<PointLink>,
                               type_var_like: TypeVarLike,
                               current_callable: Option<_>| {
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
                        if let Some(usage) = known_type_vars.find(&type_var_like, self.as_link()) {
                            return TypeVarCallbackReturn::TypeVarLike(usage);
                        }
                        unbound_type_vars.insert(type_var_like);
                        return TypeVarCallbackReturn::AnyDueToError;
                    }
                    if in_result_type.get()
                        && manager.position(&type_var_like).is_none()
                        && current_callable.is_none()
                    {
                        unbound_in_params.push(type_var_like.clone());
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
            TypeComputationOrigin::ParamTypeCommentOrAnnotation,
        );
        let mut star_annotation = None;
        let mut previous_param = None;
        for param in func_node.params().iter() {
            if let Some(annotation) = param.annotation() {
                let mut is_implicit_optional = false;
                if implicit_optional {
                    if let Some(default) = param.default() {
                        if default.as_code() == "None" {
                            is_implicit_optional = true;
                        }
                    }
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
            type_computation.cache_return_annotation(return_annot)
        });
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
        let type_vars = if let Some(known_type_vars) = known_type_vars {
            // TODO these are probably not always empty
            debug_assert!(type_vars.is_empty());
            known_type_vars
        } else {
            type_vars
        };
        if !unbound_in_params.is_empty() {
            if let Type::TypeVar(usage) = self.return_type(i_s).as_ref() {
                if unbound_in_params.contains(&TypeVarLike::TypeVar(usage.type_var.clone())) {
                    let node_ref = self.expect_return_annotation_node_ref();
                    node_ref.add_issue(i_s, IssueKind::TypeVarInReturnButNotArgument);
                    if let TypeVarKind::Bound(bound) = usage.type_var.kind(i_s.db) {
                        node_ref.add_issue(
                            i_s,
                            IssueKind::Note(
                                format!(
                                    "Consider using the upper bound \"{}\" instead",
                                    bound.format_short(i_s.db)
                                )
                                .into(),
                            ),
                        );
                    }
                }
            }
        }
        for type_var_like in unbound_type_vars.into_iter() {
            self.add_issue_for_declaration(
                i_s,
                IssueKind::TypeParametersShouldBeDeclared { type_var_like },
            );
        }
        (type_vars, type_guard, star_annotation)
    }

    pub fn return_type(&self, i_s: &InferenceState<'db, '_>) -> Cow<'file, Type> {
        self.return_annotation()
            .map(|a| {
                self.file
                    .name_resolution_for_types(i_s)
                    .use_cached_return_annotation_type(a)
            })
            .unwrap_or_else(|| Cow::Borrowed(&Type::Any(AnyCause::Unannotated)))
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
