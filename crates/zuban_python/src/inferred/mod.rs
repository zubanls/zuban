mod attribute_kind;
mod binding_utils;
mod class_binding;
mod instance_binding;

use std::{borrow::Cow, sync::Arc};

use num_bigint::BigInt;
use parsa_python_cst::NodeIndex;
use vfs::FileIndex;

use crate::{
    arguments::{CombinedArgs, KnownArgs},
    file::{
        ANNOTATION_TO_EXPR_DIFFERENCE, maybe_saved_annotation, on_argument_type_error,
        should_add_deprecated, use_cached_annotation_or_type_comment,
    },
    getitem::SliceType,
    matching::{
        ErrorStrs, Generics, IteratorContent, LookupKind, OnLookupError, OnTypeError,
        maybe_replace_class_type_vars,
    },
    new_class,
    prelude::*,
    type_::{
        ClassGenerics, DbBytes, GenericClass, InferredTypeGatherer, IterCause, IterInfos,
        LookupArgs, NeverCause, execute_tuple_class, execute_type_of_type,
    },
    type_helpers::{
        BoundMethod, BoundMethodFunction, FirstParamProperties, Function, LookupDetails,
        OverloadedFunction, execute_assert_type, execute_cast, execute_isinstance,
        execute_issubclass, execute_reveal_type, execute_super,
    },
};

pub(crate) use attribute_kind::*;
pub(crate) use binding_utils::infer_class_method;
pub(crate) use class_binding::*;
pub(crate) use instance_binding::*;

pub const NAME_DEF_TO_DEFAULTDICT_DIFF: i64 = -1;

#[derive(Debug)]
pub(crate) enum FunctionOrOverload<'a> {
    Function(Function<'a, 'a>),
    Callable(Arc<CallableContent>),
    Overload(OverloadedFunction<'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState {
    Saved(PointLink),
    UnsavedFileReference(FileIndex),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
    BoundMethod(BoundMethodState),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct BoundMethodState {
    pub instance: Type,
    mro_index: MroIndex,
    pub func_link: PointLink,
}

#[derive(Clone, Debug)]
pub(crate) struct Inferred {
    state: InferredState,
}

impl<'db: 'slf, 'slf> Inferred {
    pub fn new_and_save(file: &'db PythonFile, node_index: NodeIndex, point: Point) -> Self {
        file.points.set(node_index, point);
        Self::new_saved(file, node_index)
    }

    pub fn from_saved_node_ref(node_ref: NodeRef) -> Self {
        Self::from_saved_link(node_ref.as_link())
    }

    pub fn from_saved_link(link: PointLink) -> Self {
        Self {
            state: InferredState::Saved(link),
        }
    }

    pub fn new_saved(file: &'db PythonFile, node_index: NodeIndex) -> Self {
        Self {
            state: InferredState::Saved(PointLink::new(file.file_index, node_index)),
        }
    }

    pub fn new_unsaved_complex(complex: ComplexPoint) -> Self {
        Self {
            state: InferredState::UnsavedComplex(complex),
        }
    }

    pub const fn new_cycle() -> Self {
        Self::new_unsaved_specific(Specific::Cycle)
    }

    pub const fn new_none() -> Self {
        Self::new_unsaved_specific(Specific::None)
    }

    pub const fn new_invalid_type_definition() -> Self {
        Self::new_unsaved_specific(Specific::InvalidTypeDefinition)
    }

    pub const fn new_module_not_found() -> Self {
        Self::new_unsaved_specific(Specific::ModuleNotFound)
    }

    const fn new_unsaved_specific(specific: Specific) -> Self {
        Self {
            state: InferredState::UnsavedSpecific(specific),
        }
    }

    pub fn new_object(db: &Database) -> Self {
        Self::from_type(db.python_state.object_type())
    }

    pub fn new_list_of(db: &Database, inner: Type) -> Self {
        Self::from_type(new_class!(db.python_state.list_node_ref().as_link(), inner,))
    }

    pub const fn new_any_from_error() -> Self {
        Self::from_type(Type::ERROR)
    }

    pub fn new_any(cause: AnyCause) -> Self {
        Self::from_type(Type::Any(cause))
    }

    pub fn new_never(cause: NeverCause) -> Self {
        Self::from_type(Type::Never(cause))
    }

    pub fn new_bool(db: &Database) -> Self {
        Self::from_type(db.python_state.bool_type())
    }

    pub fn new_file_reference(index: FileIndex) -> Self {
        // TODO maybe remove this and UnsavedFileReference??? unused??
        Self {
            state: InferredState::UnsavedFileReference(index),
        }
    }

    pub const fn from_type(t: Type) -> Self {
        Self {
            state: InferredState::UnsavedComplex(ComplexPoint::TypeInstance(t)),
        }
    }

    pub fn as_cow_type(&'slf self, i_s: &InferenceState<'db, '_>) -> Cow<'slf, Type> {
        match &self.state {
            InferredState::Saved(definition) => saved_as_type(i_s, *definition),
            InferredState::UnsavedComplex(complex) => type_of_complex(i_s, complex, None),
            InferredState::UnsavedSpecific(specific) => match specific {
                Specific::None | Specific::PartialNone => Cow::Borrowed(&Type::None),
                Specific::Cycle | Specific::ModuleNotFound | Specific::InvalidTypeDefinition => {
                    Cow::Borrowed(&Type::ERROR)
                }
                Specific::PartialList => Cow::Borrowed(&i_s.db.python_state.list_of_never),
                Specific::PartialDict => Cow::Borrowed(&i_s.db.python_state.dict_of_never),
                Specific::PartialSet => Cow::Owned(new_class!(
                    i_s.db.python_state.set_node_ref().as_link(),
                    Type::Any(AnyCause::UnknownTypeParam),
                )),
                Specific::PartialDefaultDict => Cow::Owned(new_class!(
                    i_s.db.python_state.defaultdict_link(),
                    Type::Any(AnyCause::UnknownTypeParam),
                    Type::Any(AnyCause::UnknownTypeParam),
                )),
                Specific::PartialDefaultDictWithList => Cow::Owned(new_class!(
                    i_s.db.python_state.defaultdict_link(),
                    Type::Any(AnyCause::UnknownTypeParam),
                    i_s.db.python_state.list_of_never.clone(),
                )),
                Specific::PartialDefaultDictWithSet => Cow::Owned(new_class!(
                    i_s.db.python_state.defaultdict_link(),
                    Type::Any(AnyCause::UnknownTypeParam),
                    new_class!(
                        i_s.db.python_state.set_node_ref().as_link(),
                        Type::Any(AnyCause::UnknownTypeParam),
                    )
                )),
                _ => {
                    recoverable_error!("UnsavedSpecific {specific:?} type should not be handled");
                    Cow::Borrowed(&Type::ERROR)
                }
            },
            InferredState::UnsavedFileReference(file_index) => {
                Cow::Owned(Type::Module(*file_index))
            }
            InferredState::BoundMethod(BoundMethodState {
                instance,
                mro_index,
                func_link,
            }) => {
                let class = Self::load_bound_method_class(i_s, instance, *mro_index);
                Cow::Owned(load_bound_method(i_s, instance, class, *func_link).as_type(i_s))
            }
        }
    }

    pub fn as_type(&self, i_s: &InferenceState) -> Type {
        self.as_cow_type(i_s).into_owned()
    }

    pub fn format_short(&self, i_s: &InferenceState) -> Box<str> {
        if let Some(specific) = self.maybe_saved_specific(i_s.db) {
            match specific {
                Specific::PartialList => return "List[<Partial>]".into(),
                Specific::PartialDict => return "Dict[<Partial>, <Partial>]".into(),
                Specific::PartialSet => return "Set[<Partial>]".into(),
                _ => (),
            }
        }
        self.as_cow_type(i_s).format_short(i_s.db)
    }

    pub fn maybe_saved_link(&self) -> Option<PointLink> {
        match self.state {
            InferredState::Saved(definition) => Some(definition),
            _ => None,
        }
    }

    pub fn maybe_saved_node_ref(&self, db: &'db Database) -> Option<NodeRef<'db>> {
        self.maybe_saved_link()
            .map(|link| NodeRef::from_link(db, link))
    }

    pub fn is_name_defined_in_module(
        &self,
        db: &'db Database,
        module_name: &str,
        symbol_name: &str,
    ) -> bool {
        self.maybe_saved_node_ref(db).is_some_and(|node_ref| {
            node_ref.is_name_defined_in_module(db, module_name, symbol_name)
        })
    }

    pub fn maybe_specific(&self, db: &Database) -> Option<Specific> {
        if let InferredState::UnsavedSpecific(specific) = &self.state {
            return Some(*specific);
        }
        self.maybe_saved_node_ref(db)
            .and_then(|node_ref| node_ref.point().maybe_specific())
    }

    pub fn maybe_saved_specific(&self, db: &Database) -> Option<Specific> {
        self.maybe_saved_node_ref(db)
            .and_then(|node_ref| node_ref.point().maybe_specific())
    }

    pub fn maybe_type_guard_callable(&self, i_s: &InferenceState) -> Option<CallableLike> {
        if self.maybe_saved_specific(i_s.db) == Some(Specific::Function) {
            // Normal functions are never type guards. To avoid moving that into a Callable (for
            // performance), we can just return here.
            return None;
        }
        self.as_cow_type(i_s).maybe_callable(i_s)
    }

    pub fn maybe_new_partial(
        &self,
        i_s: &InferenceState,
        set_defaultdict_type: impl Fn(Type),
    ) -> Option<Inferred> {
        if self.maybe_saved_specific(i_s.db) == Some(Specific::None)
            || matches!(
                self.state,
                InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Type::None))
            )
        {
            return Some(Inferred::new_unsaved_specific(Specific::PartialNone));
        }
        let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(i_s.db) else {
            return None;
        };
        Self::maybe_new_partial_point_internal(i_s, t, set_defaultdict_type).map(|specific| {
            Inferred {
                state: InferredState::UnsavedSpecific(specific),
            }
        })
    }

    pub fn maybe_any_with_unknown_type_params(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
    ) -> Option<Inferred> {
        let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(i_s.db) else {
            return None;
        };
        t.has_any_with_unknown_type_params(i_s.db).then(|| {
            if !i_s.db.project.flags.allow_incomplete_generics && !i_s.in_untyped_context() {
                let for_ = from.as_code();
                // Mypy does not enforce a type annotation for _
                if for_ != "_" {
                    from.add_issue(
                        i_s,
                        IssueKind::NeedTypeAnnotation {
                            for_: for_.into(),
                            hint: None,
                        },
                    );
                }
            }
            Inferred::from_type(
                t.replace_any_with_unknown_type_params_with_any()
                    .unwrap_or_else(|| t.clone()),
            )
        })
    }

    pub fn maybe_new_nullable_partial_point(
        &self,
        i_s: &InferenceState,
        set_defaultdict_type: impl Fn(Type),
    ) -> Option<Point> {
        let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(i_s.db) else {
            return None;
        };
        Self::maybe_new_partial_point_internal(i_s, t, set_defaultdict_type).map(|specific| {
            let mut p = Point::new_specific(specific, Locality::Todo);
            let mut flags = p.partial_flags();
            flags.nullable = true;
            p = p.set_partial_flags(flags);
            p
        })
    }

    fn maybe_new_partial_point_internal(
        i_s: &InferenceState,
        t: &Type,
        set_defaultdict_type: impl Fn(Type),
    ) -> Option<Specific> {
        let Type::Class(
            c @ GenericClass {
                link,
                generics: ClassGenerics::List(generics),
            },
        ) = t
        else {
            return None;
        };
        let specific = if *link == i_s.db.python_state.list_node_ref().as_link() {
            Specific::PartialList
        } else if *link == i_s.db.python_state.dict_node_ref().as_link() {
            Specific::PartialDict
        } else if *link == i_s.db.python_state.set_node_ref().as_link() {
            Specific::PartialSet
        } else if *link == i_s.db.python_state.defaultdict_link() {
            let cls = c.class(i_s.db);
            let first = cls.nth_type_argument(i_s.db, 0);
            if matches!(first, Type::Any(AnyCause::UnknownTypeParam)) {
                let second = cls.nth_type_argument(i_s.db, 1);
                fn dont_set_type(_: Type) {}
                return match Self::maybe_new_partial_point_internal(i_s, &second, dont_set_type) {
                    Some(Specific::PartialList) => Some(Specific::PartialDefaultDictWithList),
                    Some(Specific::PartialSet) => Some(Specific::PartialDefaultDictWithSet),
                    _ => {
                        if second.has_any_with_unknown_type_params(i_s.db) {
                            None
                        } else {
                            set_defaultdict_type(second);
                            Some(Specific::PartialDefaultDict)
                        }
                    }
                };
            }
            return None;
        } else {
            return None;
        };
        for generic in generics.iter() {
            if !matches!(
                generic,
                Generic::TypeArg(Type::Any(AnyCause::UnknownTypeParam))
            ) {
                return None;
            }
        }
        Some(specific)
    }

    pub fn resolve_class_type_vars(
        self,
        i_s: &InferenceState,
        class: &Class,
        attribute_class: &Class,
    ) -> Self {
        if let InferredState::Saved(link) = self.state {
            let definition = NodeRef::from_link(i_s.db, link);
            if let Some(specific) = definition.point().maybe_specific() {
                match specific {
                    Specific::AnnotationOrTypeCommentWithTypeVars
                    | Specific::AnnotationOrTypeCommentFinal => {
                        let t = use_cached_annotation_or_type_comment(i_s, definition);
                        if attribute_class.needs_generic_remapping_for_attributes(i_s, &t)
                            && let Some(d) =
                                maybe_replace_class_type_vars(i_s.db, &t, attribute_class, &|| {
                                    Some(class.as_type(i_s.db))
                                })
                        {
                            return Inferred::from_type(d);
                        }
                    }
                    _ => (),
                }
            } else if let Some(t) = definition.maybe_type()
                && let Some(d) = maybe_replace_class_type_vars(i_s.db, t, attribute_class, &|| {
                    Some(class.as_type(i_s.db))
                })
            {
                return Inferred::from_type(d);
            }
        }
        self
    }

    pub fn maybe_complex_point(&'slf self, db: &'db Database) -> Option<&'slf ComplexPoint> {
        match &self.state {
            InferredState::Saved(definition) => NodeRef::from_link(db, *definition).maybe_complex(),
            InferredState::UnsavedComplex(t) => Some(t),
            _ => None,
        }
    }

    pub fn maybe_file(&self, db: &'db Database) -> Option<FileIndex> {
        if let InferredState::UnsavedFileReference(file) = self.state {
            Some(file)
        } else if let Some(f) = self
            .maybe_saved_node_ref(db)
            .and_then(|n| n.point().maybe_file_reference())
        {
            Some(f)
        } else if let Type::Module(m) = self
            .maybe_complex_point(db)
            .and_then(|c| c.maybe_instance())?
        {
            Some(*m)
        } else {
            None
        }
    }

    pub fn maybe_bound_method(&self) -> Option<&BoundMethodState> {
        match &self.state {
            InferredState::BoundMethod(bound) => Some(bound),
            _ => None,
        }
    }

    pub fn maybe_literal(
        &'slf self,
        db: &'db Database,
    ) -> UnionValue<Literal, impl Iterator<Item = Literal> + 'slf> {
        let from_type = |t: &'slf Type| match t {
            Type::Union(t) => match t.iter().next() {
                Some(Type::Literal(_)) => UnionValue::Multiple(t.iter().map_while(|t| match t {
                    Type::Literal(literal) => Some(literal.clone()),
                    _ => None,
                })),
                _ => UnionValue::Any,
            },
            Type::Literal(literal) => UnionValue::Single(literal.clone()),
            _ => UnionValue::Any,
        };
        if let InferredState::Saved(link) = self.state {
            let node_ref = NodeRef::from_link(db, link);
            match node_ref.point().maybe_specific() {
                Some(Specific::IntLiteral) => {
                    return UnionValue::Single(Literal {
                        kind: LiteralKind::Int(node_ref.expect_int().parse()),
                        implicit: true,
                    });
                }
                Some(Specific::StringLiteral) => {
                    return UnionValue::Single(Literal {
                        kind: LiteralKind::String(
                            DbString::from_python_string(
                                node_ref.file_index(),
                                node_ref.maybe_str().unwrap().as_python_string(),
                            )
                            .unwrap(),
                        ),
                        implicit: true,
                    });
                }
                _ => (),
            }
            if let Some(t) = maybe_saved_annotation(node_ref) {
                return from_type(t);
            }
        }
        if let Some(t) = self
            .maybe_complex_point(db)
            .and_then(|c| c.maybe_instance())
        {
            from_type(t)
        } else {
            UnionValue::Any
        }
    }

    pub fn run_on_int_literals(
        &self,
        i_s: &InferenceState,
        callable: impl Fn(&BigInt) -> Option<Inferred>,
    ) -> Option<Inferred> {
        let infer = |i_s: &InferenceState, literal: Literal| {
            if !matches!(literal.kind, LiteralKind::Int(_)) {
                return None;
            }
            let LiteralValue::Int(i) = literal.value(i_s.db) else {
                unreachable!();
            };
            callable(i)
        };
        match self.maybe_literal(i_s.db) {
            UnionValue::Single(literal) => infer(i_s, literal),
            UnionValue::Multiple(literals) => {
                let mut gatherer = InferredTypeGatherer::default();
                for literal in literals {
                    gatherer.add(infer(i_s, literal)?)
                }
                gatherer.into_inferred_if_not_never(i_s)
            }
            UnionValue::Any => None,
        }
    }

    pub fn run_on_str_literals(
        &self,
        i_s: &InferenceState,
        callable: impl Fn(&str) -> Option<Inferred>,
    ) -> Option<Inferred> {
        let infer = |i_s: &InferenceState, literal: Literal| {
            if !matches!(literal.kind, LiteralKind::String(_)) {
                return None;
            }
            let LiteralValue::String(s) = literal.value(i_s.db) else {
                unreachable!();
            };
            callable(s)
        };
        match self.maybe_literal(i_s.db) {
            UnionValue::Single(literal) => infer(i_s, literal),
            UnionValue::Multiple(literals) => {
                let mut gatherer = InferredTypeGatherer::default();
                for literal in literals {
                    gatherer.add(infer(i_s, literal)?)
                }
                gatherer.into_inferred_if_not_never(i_s)
            }
            UnionValue::Any => None,
        }
    }

    pub fn maybe_bool_literal(&self, i_s: &InferenceState) -> Option<bool> {
        if let Type::Literal(Literal {
            kind: LiteralKind::Bool(b),
            ..
        }) = self.as_cow_type(i_s).as_ref()
        {
            Some(*b)
        } else {
            None
        }
    }

    pub fn maybe_string_literal(&self, i_s: &InferenceState) -> Option<DbString> {
        if let Type::Literal(Literal {
            kind: LiteralKind::String(b),
            ..
        }) = self.as_cow_type(i_s).as_ref()
        {
            Some(b.clone())
        } else {
            None
        }
    }

    pub fn save_redirect(self, i_s: &InferenceState, file: &PythonFile, index: NodeIndex) -> Self {
        self.maybe_save_redirect(i_s, file, index, false)
    }

    pub fn maybe_save_redirect(
        self,
        i_s: &InferenceState,
        file: &PythonFile,
        index: NodeIndex,
        ignore_if_already_saved: bool,
    ) -> Self {
        // TODO this locality should be calculated in a more correct way
        let p = file.points.get(index);
        if p.calculated() && p.maybe_specific() == Some(Specific::Cycle) {
            return Self::new_saved(file, index);
        }
        let point = match self.state {
            InferredState::Saved(definition) => {
                // Overwriting strings needs to be possible, because of string annotations
                if p.calculated()
                    && !matches!(
                        p.maybe_specific(),
                        // TODO AnyDueToError can maybe be removed again if match is implemented
                        Some(Specific::String | Specific::Cycle | Specific::AnyDueToError)
                    )
                {
                    if ignore_if_already_saved {
                        return self;
                    }
                    if std::cfg!(debug_assertions) {
                        let node_ref = NodeRef::new(file, index);
                        panic!(
                            "Why overwrite? New: {:?} Previous: {:?} on {}:{}",
                            self.debug_info(i_s.db),
                            node_ref.debug_info(i_s.db),
                            file.file_path_with_scheme(i_s.db).as_uri(),
                            node_ref.line_one_based(i_s.db)
                        );
                    }
                }
                file.points.set(
                    index,
                    Point::new_redirect(definition.file, definition.node_index, Locality::Todo),
                );
                return self;
            }
            InferredState::UnsavedComplex(complex) => match complex {
                ComplexPoint::TypeInstance(Type::None) => {
                    Point::new_specific(Specific::None, Locality::Todo)
                }
                ComplexPoint::TypeInstance(Type::Any(AnyCause::FromError)) => {
                    Point::new_specific(Specific::AnyDueToError, Locality::Todo)
                }
                _ => {
                    file.complex_points
                        .insert(&file.points, index, complex, Locality::Todo);
                    return Self::new_saved(file, index);
                }
            },
            InferredState::UnsavedSpecific(mut specific) => {
                if specific == Specific::Cycle {
                    let r = NodeRef::new(file, index);
                    r.add_issue(
                        i_s,
                        IssueKind::CyclicDefinition {
                            name: Box::from(r.as_code()),
                        },
                    );
                    specific = Specific::AnyDueToError;
                }
                Point::new_specific(specific, Locality::Todo)
            }
            InferredState::UnsavedFileReference(file_index) => {
                Point::new_file_reference(file_index, Locality::Todo)
            }
            InferredState::BoundMethod(BoundMethodState {
                instance,
                mro_index,
                func_link,
            }) => {
                let class = Self::load_bound_method_class(i_s, &instance, mro_index);
                let bound_method = load_bound_method(i_s, &instance, class, func_link);
                file.complex_points.insert(
                    &file.points,
                    index,
                    ComplexPoint::TypeInstance(bound_method.as_type(i_s)),
                    Locality::Todo,
                );
                return Self::new_saved(file, index);
            }
        };
        file.points.set(index, point);
        Self::new_saved(file, index)
    }

    pub(crate) fn init_as_function<'a>(
        &self,
        i_s: &InferenceState<'db, '_>,
        class: Option<Class<'a>>,
    ) -> FunctionOrOverload<'a>
    where
        'db: 'a,
    {
        match &self.state {
            InferredState::Saved(link) => {
                let definition = NodeRef::from_link(i_s.db, *link);
                if definition.point().maybe_specific() == Some(Specific::Function) {
                    return FunctionOrOverload::Function(Function::new(definition, class));
                }
                match definition.maybe_complex() {
                    Some(ComplexPoint::FunctionOverload(overload)) => {
                        return FunctionOrOverload::Overload(OverloadedFunction::new(
                            &overload.functions,
                            class,
                        ));
                    }
                    Some(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                        return FunctionOrOverload::Callable(c.clone());
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(c) => {
                if let Some(Type::Callable(c)) = c.maybe_instance() {
                    return FunctionOrOverload::Callable(c.clone());
                }
            }
            _ => (),
        }
        FunctionOrOverload::Callable(i_s.db.python_state.any_callable_from_error.clone())
    }

    pub fn avoid_implicit_literal(self, i_s: &InferenceState) -> Self {
        self.maybe_avoid_implicit_literal(i_s).unwrap_or(self)
    }

    pub fn maybe_avoid_implicit_literal(&self, i_s: &InferenceState) -> Option<Self> {
        if i_s.is_calculating_enum_members() {
            return None;
        }
        match self.state {
            InferredState::Saved(link) => {
                let node_ref = NodeRef::from_link(i_s.db, link);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::MaybeSelfParam => {
                            return Some(Inferred::from_type(i_s.current_type().unwrap()));
                        }
                        Specific::IntLiteral
                        | Specific::StringLiteral
                        | Specific::BytesLiteral
                        | Specific::BoolLiteral
                        | Specific::AnnotationOrTypeCommentFinal => (),
                        _ => return None,
                    },
                    PointKind::Complex => {
                        if node_ref.maybe_complex().unwrap().maybe_instance().is_none() {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(_)) => (),
            _ => return None,
        }
        if let Some(t) = self.as_cow_type(i_s).maybe_avoid_implicit_literal(i_s.db) {
            Some(Self::from_type(t))
        } else {
            None
        }
    }

    #[inline]
    pub fn gather_simplified_union(
        i_s: &InferenceState,
        callable: impl FnOnce(&mut dyn FnMut(Self)),
    ) -> Self {
        let mut gatherer = InferredTypeGatherer::default();
        callable(&mut |inferred| gatherer.add(inferred));
        gatherer.into_inferred(i_s)
    }

    pub fn simplified_union(self, i_s: &InferenceState, other: Self) -> Self {
        Inferred::from_type(
            self.as_cow_type(i_s)
                .simplified_union(i_s, &other.as_cow_type(i_s)),
        )
    }

    #[inline]
    pub fn gather_base_types(
        i_s: &InferenceState,
        callable: impl FnOnce(&mut dyn FnMut(Self)),
    ) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |inferred| {
            *r = Some(match r.take() {
                Some(i) => i.common_base_type(i_s, &inferred),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| Inferred::new_never(NeverCause::Other))
    }

    fn common_base_type(&self, i_s: &InferenceState, other: &Self) -> Self {
        Self::from_type(
            self.as_cow_type(i_s)
                .common_base_type(i_s, &other.as_cow_type(i_s)),
        )
    }

    pub fn debug_info(&self, db: &Database) -> String {
        fn format_complex(db: &Database, from: Option<NodeRef>, complex: &ComplexPoint) -> String {
            match complex {
                ComplexPoint::TypeInstance(t) => t.format_short(db).into(),
                ComplexPoint::Class(_) => {
                    format!(
                        "ClassDefinition({}, {})",
                        from.unwrap().maybe_class().unwrap().name().as_code(),
                        from.unwrap().debug_info(db)
                    )
                }
                ComplexPoint::ClassInfos(_) => {
                    format!("ClassInfos({})", from.unwrap().debug_info(db))
                }
                ComplexPoint::TypeVarLikes(_) => {
                    format!("TypeVarLikes({})", from.unwrap().debug_info(db))
                }
                ComplexPoint::FunctionOverload(_) => {
                    format!("OverloadedFunction({})", from.unwrap().debug_info(db))
                }
                ComplexPoint::NamedTupleDefinition(t) => {
                    format!("NamedTupleDef({})", t.format_short(db))
                }
                ComplexPoint::TypedDictDefinition(td) => {
                    format!("TypedDictDef({})", td.type_.format_short(db))
                }
                ComplexPoint::IndirectFinal(t) => {
                    format!("IndirectFinal({})", t.format_short(db))
                }
                ComplexPoint::TypeVarLike(tvl) => {
                    format!("TypeVarLike({})", tvl.name(db))
                }
                ComplexPoint::TypeAlias(alias) => {
                    format!(
                        "TypeAlias({}, {})",
                        alias.name(db),
                        from.unwrap().debug_info(db)
                    )
                }
                ComplexPoint::WidenedType(widened) => {
                    format!(
                        "WidenedType(original={}, widened={})",
                        format_complex(db, from, &widened.original),
                        widened.widened.format_short(db)
                    )
                }
                ComplexPoint::PyTypedMissing(_) => "PyTypedMissing(...)".into(),
                ComplexPoint::HeuristicBound(heuristic) => {
                    format!(
                        "HeuristicBound(type={}, bound={})",
                        heuristic.type_.format_short(db),
                        heuristic.bound_to.format_short(db),
                    )
                }
            }
        }
        match &self.state {
            InferredState::Saved(definition) => {
                let from = NodeRef::from_link(db, *definition);
                let p = from.point();
                match p.kind() {
                    PointKind::Specific => format!("Specific({:?})", p.specific()),
                    PointKind::Complex => {
                        let complex = from.file.complex_points.get(p.complex_index());
                        format_complex(db, Some(from), complex)
                    }
                    PointKind::FileReference => format!("UnsavedFile({})", p.file_index()),
                    PointKind::Redirect => unreachable!(),
                }
            }
            InferredState::UnsavedFileReference(file_index) => format!("UnsavedFile({file_index})"),
            InferredState::UnsavedComplex(c) => format!("Unsaved({})", format_complex(db, None, c)),
            InferredState::UnsavedSpecific(specific) => format!("UnsavedSpecific({specific:?})"),
            InferredState::BoundMethod(BoundMethodState {
                instance,
                func_link,
                ..
            }) => {
                format!(
                    "BoundMethod({}.{})",
                    instance.format_short(db),
                    Function::new(NodeRef::from_link(db, *func_link), None).name()
                )
            }
        }
    }

    pub fn is_union_like(&self, i_s: &InferenceState) -> bool {
        self.as_cow_type(i_s).is_union_like(i_s.db)
    }

    pub fn is_never(&self, i_s: &InferenceState) -> bool {
        self.as_cow_type(i_s).is_never()
    }

    pub fn maybe_any(&self, db: &Database) -> Option<AnyCause> {
        if let Some(complex) = self.maybe_complex_point(db) {
            return match complex.maybe_instance() {
                Some(Type::Any(cause)) => Some(*cause),
                _ => None,
            };
        }

        match self.maybe_saved_specific(db)? {
            Specific::AnyDueToError
            | Specific::Cycle
            | Specific::InvalidTypeDefinition
            | Specific::BinaryExtension => Some(AnyCause::FromError),
            Specific::AnnotationOrTypeCommentWithoutTypeVars => Some(AnyCause::FromError),
            Specific::ModuleNotFound => Some(AnyCause::ModuleNotFound),
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        in_file: &PythonFile,
        name: &str,
        kind: LookupKind,
        add_issue: &dyn Fn(IssueKind) -> bool,
        callable: &mut impl FnMut(&Type, LookupDetails),
    ) {
        self.as_cow_type(i_s).run_after_lookup_on_each_union_member(
            Some(self),
            LookupArgs::new(i_s, in_file, name)
                .with_kind(kind)
                .with_add_issue(add_issue),
            &mut ResultContext::ValueExpected,
            callable,
        )
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        self.lookup_with_result_context(
            i_s,
            node_ref,
            name,
            kind,
            &mut ResultContext::ValueExpected,
        )
    }

    pub fn lookup_with_result_context(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
    ) -> LookupResult {
        let base_type = self.as_cow_type(i_s);
        base_type.lookup(
            i_s,
            from.file,
            name,
            kind,
            result_context,
            &|issue| from.add_issue(i_s, issue),
            &|t| add_attribute_error(i_s, from, &base_type, t, name),
        )
    }

    pub(crate) fn type_lookup_and_execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        in_file: &PythonFile,
        name: &str,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_lookup_error: OnLookupError,
    ) -> Self {
        self.type_lookup_and_execute_with_details(
            i_s,
            in_file,
            name,
            args,
            result_context,
            &|issue| args.add_issue(i_s, issue),
            on_lookup_error,
            OnTypeError::new(&on_argument_type_error),
        )
    }

    pub(crate) fn type_lookup_and_execute_with_attribute_error(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
    ) -> Self {
        self.type_lookup_and_execute(i_s, from.file, name, args, result_context, &|t| {
            add_attribute_error(i_s, from, &self.as_cow_type(i_s), t, name)
        })
    }

    fn type_lookup_and_execute_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        in_file: &PythonFile,
        name: &str,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
        on_lookup_error: OnLookupError,
        on_type_error: OnTypeError,
    ) -> Self {
        let mut gatherer = InferredTypeGatherer::default();
        self.run_after_lookup_on_each_union_member(
            i_s,
            in_file,
            name,
            LookupKind::OnlyType,
            add_issue,
            &mut |_, lookup_result| {
                if matches!(lookup_result.lookup, LookupResult::None) {
                    on_lookup_error(&self.as_cow_type(i_s));
                }
                let inf = lookup_result.lookup.into_inferred().execute_with_details(
                    i_s,
                    args,
                    result_context,
                    on_type_error,
                );
                gatherer.add(inf)
            },
        );
        gatherer.into_inferred(i_s)
    }

    pub(crate) fn execute(&self, i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Self {
        self.execute_with_details(
            i_s,
            args,
            &mut ResultContext::ValueExpected,
            OnTypeError::new(&on_argument_type_error),
        )
    }

    pub(crate) fn execute_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Self {
        match &self.state {
            InferredState::Saved(link) => {
                let node_ref = NodeRef::from_link(i_s.db, *link);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => {
                        macro_rules! return_on_type_def {
                            ($name:ident $(, $args:expr )?) => {
                                if let ResultContext::AssignmentNewDefinition {
                                    assignment_definition,
                                } = &result_context
                                {
                                    debug!("Execute type definition with {}", stringify!($name));
                                    return assignment_definition.file(i_s.db)
                                        .name_resolution_for_types(i_s)
                                        .$name($($args)?);
                                }
                            };
                        }

                        let specific = point.specific();
                        match specific {
                            Specific::Function => {
                                return Function::new(node_ref, None).execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                );
                            }
                            Specific::BuiltinsSuper => return execute_super(i_s, args),
                            Specific::BuiltinsIsinstance => return execute_isinstance(i_s, args),
                            Specific::BuiltinsIssubclass => return execute_issubclass(i_s, args),
                            Specific::TypingTypeVarClass => {
                                return_on_type_def!(compute_type_var_assignment, args);
                                if result_context.is_annotation_assignment() {
                                    args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
                                }
                            }
                            Specific::TypingTypeVarTupleClass => {
                                return_on_type_def!(compute_type_var_tuple_assignment, args);
                                if result_context.is_annotation_assignment() {
                                    args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
                                }
                            }
                            Specific::TypingParamSpecClass => {
                                return_on_type_def!(compute_param_spec_assignment, args);
                                if result_context.is_annotation_assignment() {
                                    args.add_issue(i_s, IssueKind::UnexpectedTypeForTypeVar);
                                }
                            }
                            Specific::BuiltinsSentinel => {
                                return_on_type_def!(compute_sentinel_assignment, args);
                            }
                            Specific::TypingNewType
                                if result_context.is_annotation_assignment() =>
                            {
                                args.add_issue(i_s, IssueKind::NewTypeCannotHaveTypeDeclaration);
                                return Inferred::new_any(AnyCause::FromError);
                            }
                            Specific::TypingTypedDict
                            | Specific::TypingNamedTuple
                            | Specific::TypingNewType => {
                                if let ResultContext::AssignmentNewDefinition {
                                    assignment_definition,
                                } = &result_context
                                {
                                    return assignment_definition
                                        .file(i_s.db)
                                        .name_resolution_for_types(i_s)
                                        .compute_special_alias_assignment(
                                            specific,
                                            assignment_definition.as_node(i_s.db),
                                        );
                                }
                            }
                            Specific::CollectionsNamedTuple => {
                                return_on_type_def!(compute_collections_named_tuple, args)
                            }
                            Specific::TypingTuple => {
                                return execute_tuple_class(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                );
                            }
                            Specific::TypingCast => return execute_cast(i_s, args),
                            Specific::RevealTypeFunction => {
                                return execute_reveal_type(i_s, args, result_context);
                            }
                            Specific::AssertTypeFunction => {
                                return execute_assert_type(i_s, args, result_context);
                            }
                            Specific::TypingTypeAliasType => {
                                if let ResultContext::AssignmentNewDefinition {
                                    assignment_definition,
                                } = &result_context
                                {
                                    if let Some(inf) = assignment_definition
                                        .file(i_s.db)
                                        .name_resolution_for_types(i_s)
                                        .execute_type_alias_from_type_alias_type(
                                            args,
                                            assignment_definition.as_node(i_s.db),
                                        )
                                    {
                                        return inf;
                                    }
                                }
                            }
                            Specific::TypingAny => {
                                args.add_issue(i_s, IssueKind::AnyNotCallable);
                                args.calculate_diagnostics_for_any_callable();
                                return Inferred::new_any_from_error();
                            }
                            Specific::MypyExtensionsArg
                            | Specific::MypyExtensionsDefaultArg
                            | Specific::MypyExtensionsNamedArg
                            | Specific::MypyExtensionsDefaultNamedArg
                            | Specific::MypyExtensionsVarArg
                            | Specific::MypyExtensionsKwArg => {
                                return i_s
                                    .db
                                    .python_state
                                    .mypy_extensions_arg_func(i_s.db, specific)
                                    .execute_with_details(
                                        i_s,
                                        args,
                                        result_context,
                                        on_type_error,
                                    );
                            }
                            Specific::TypingProtocol
                            | Specific::TypingGeneric
                            | Specific::TypingUnion
                            | Specific::TypingOptional
                            | Specific::TypingLiteral
                            | Specific::TypingAnnotated
                            | Specific::TypingCallable => {
                                args.add_issue(
                                    i_s,
                                    IssueKind::NotCallable {
                                        type_: "\"_SpecialForm\"".into(),
                                    },
                                );
                                return Inferred::new_any_from_error();
                            }
                            Specific::TypingDataclassTransform => {
                                return Inferred::new_object(i_s.db);
                            }
                            Specific::TypingTypeForm => {
                                debug!("Execute type definition with TypeForm");
                                if let Some(file) = args.in_file() {
                                    return file
                                        .name_resolution_for_types(i_s)
                                        .execute_type_form(args);
                                }
                            }
                            _ => (),
                        }
                    }
                    PointKind::Complex => {
                        match node_ref.file.complex_points.get(point.complex_index()) {
                            ComplexPoint::FunctionOverload(overload) => {
                                return OverloadedFunction::new(&overload.functions, None).execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                );
                            }
                            ComplexPoint::Class(cls) => {
                                node_ref.ensure_cached_class_infos(i_s);
                                let class_ref = ClassNodeRef::from_node_ref(node_ref);
                                let c = Class::new(
                                    class_ref,
                                    cls,
                                    Generics::NotDefinedYet { class_ref },
                                    None,
                                );
                                // We might be dealing with dataclasses or enums. In that case use
                                // the normal mechanism that creates a type first and then
                                // executes.
                                let is_class_like = match c
                                    .use_cached_class_infos(i_s.db)
                                    .undefined_generics_type
                                    .get()
                                {
                                    None => true,
                                    Some(x) => matches!(x.as_ref(), Type::Class(_)),
                                };
                                if is_class_like {
                                    return c.execute(
                                        i_s,
                                        args,
                                        result_context,
                                        on_type_error,
                                        false,
                                    );
                                }
                            }
                            ComplexPoint::TypeAlias(alias) if !alias.from_type_syntax => {
                                if !alias.is_annotated() {
                                    if !alias.type_vars.is_empty()
                                        && let Some(file) = args.in_file()
                                        && file.flags(i_s.db).disallow_any_generics
                                    {
                                        node_ref.add_issue(
                                            i_s,
                                            IssueKind::MissingTypeArguments {
                                                name: alias.name(i_s.db).into(),
                                            },
                                        );
                                    }
                                    if alias.application_allowed(i_s.db) {
                                        return execute_type_of_type(
                                            i_s,
                                            args,
                                            result_context,
                                            on_type_error,
                                            &alias.as_type_and_set_type_vars_any(i_s.db),
                                        );
                                    }
                                }
                                args.add_issue(
                                    i_s,
                                    IssueKind::NotCallable {
                                        type_: Box::from("\"<typing special form>\""),
                                    },
                                );
                                return Inferred::new_any_from_error();
                            }
                            _ => (),
                        }
                    }
                    PointKind::FileReference => {
                        args.add_issue(
                            i_s,
                            IssueKind::NotCallable {
                                type_: Box::from("Module"),
                            },
                        );
                        return Inferred::new_any_from_error();
                    }
                    _ => (),
                }
            }
            InferredState::BoundMethod(BoundMethodState {
                instance,
                mro_index,
                func_link,
            }) => {
                let class = Self::load_bound_method_class(i_s, instance, *mro_index);
                return load_bound_method(i_s, instance, class, *func_link).execute(
                    i_s,
                    args,
                    result_context,
                    on_type_error,
                );
            }
            _ => (),
        }
        self.as_cow_type(i_s)
            .execute(i_s, Some(self), args, result_context, on_type_error)
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        if let InferredState::Saved(link) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, link);
            match node_ref.point().maybe_specific() {
                Some(
                    specific @ (Specific::TypingProtocol
                    | Specific::TypingGeneric
                    | Specific::TypingTuple
                    | Specific::TypingUnion
                    | Specific::TypingOptional
                    | Specific::BuiltinsType
                    | Specific::TypingType
                    | Specific::TypingLiteral
                    | Specific::TypingAnnotated
                    | Specific::TypingCallable
                    | Specific::MypyExtensionsFlexibleAlias),
                ) => {
                    return slice_type
                        .file
                        .name_resolution_for_types(i_s)
                        .compute_type_application_on_typing_class(
                            specific,
                            *slice_type,
                            result_context,
                        );
                }
                Some(Specific::TypingNamedTuple) => {
                    // The situation around NamedTuple is weird, because it's actually a function,
                    // but in Typeshed it's a class that inherits from tuple.
                    slice_type
                        .as_node_ref()
                        .add_issue(i_s, IssueKind::OnlyClassTypeApplication);
                }
                _ => {
                    let node_ref = NodeRef::from_link(i_s.db, link);
                    if let Some(ComplexPoint::TypeAlias(ta)) = node_ref.maybe_complex() {
                        return slice_type
                            .file
                            .name_resolution_for_types(i_s)
                            .compute_type_application_on_alias(ta, *slice_type, result_context);
                    }
                }
            }
        }
        self.as_cow_type(i_s)
            .get_item(i_s, Some(self), slice_type, result_context)
    }

    pub fn type_check_set_item(
        &self,
        i_s: &InferenceState,
        slice_type: SliceType,
        value: &Inferred,
    ) {
        let from = slice_type.as_node_ref();
        debug!("Set Item on {}", self.format_short(i_s));
        let args = slice_type.as_args(*i_s);
        self.type_lookup_and_execute_with_details(
            i_s,
            from.file,
            "__setitem__",
            &CombinedArgs::new(&args, &KnownArgs::new(value, from)),
            &mut ResultContext::ExpectUnused,
            &|issue| from.add_issue(i_s, issue),
            &|_| {
                slice_type.as_node_ref().add_issue(
                    i_s,
                    IssueKind::UnsupportedSetItemTarget(self.format_short(i_s)),
                );
            },
            OnTypeError::new(&|i_s, _, arg, types| {
                let ErrorStrs { got, expected } = types.as_boxed_strs(i_s.db);
                let type_ = if arg.index == 1 {
                    IssueKind::InvalidGetItem {
                        type_: self.format_short(i_s),
                        actual: got,
                        expected,
                    }
                } else {
                    IssueKind::InvalidSetItemTarget { got, expected }
                };
                from.add_issue(i_s, type_);
            }),
        );
    }

    #[inline]
    pub fn add_issue_if_final_assignment(
        &self,
        i_s: &InferenceState,
        from: NodeRef,
        name: &str,
        is_attribute: bool,
    ) -> bool {
        let result = self.maybe_saved_specific(i_s.db)
            == Some(Specific::AnnotationOrTypeCommentFinal)
            || matches!(
                self.maybe_complex_point(i_s.db),
                Some(ComplexPoint::IndirectFinal(_))
            );
        if result {
            from.add_issue(
                i_s,
                IssueKind::CannotAssignToFinal {
                    is_attribute,
                    name: name.into(),
                },
            );
        }
        result
    }

    pub fn iter(self, i_s: &InferenceState, from: NodeRef, cause: IterCause) -> IteratorContent {
        self.as_cow_type(i_s).iter(
            i_s,
            IterInfos::new(from, cause, &|issue| from.add_issue(i_s, issue)),
        )
    }

    pub fn is_saved(&self) -> bool {
        matches!(&self.state, InferredState::Saved(_))
    }

    pub fn is_saved_partial(&self, db: &Database) -> bool {
        self.maybe_saved_specific(db)
            .is_some_and(|specific| specific.is_partial())
    }

    pub fn is_saved_partial_container(&self, db: &Database) -> bool {
        self.maybe_saved_specific(db)
            .is_some_and(|specific| specific.is_partial_container())
    }

    pub fn is_unsaved_module_not_found(&self) -> bool {
        matches!(
            self.state,
            InferredState::UnsavedSpecific(Specific::ModuleNotFound)
        )
    }

    pub fn remove_none(&self, i_s: &InferenceState) -> Self {
        Inferred::from_type(self.as_type(i_s).remove_none(i_s.db).into_owned())
    }

    pub fn remove_final(&self, i_s: &InferenceState) -> Option<Self> {
        if let InferredState::Saved(link) = self.state {
            let n = NodeRef::from_link(i_s.db, link);
            if n.point().maybe_specific() == Some(Specific::AnnotationOrTypeCommentFinal) {
                debug_assert!(
                    n.add_to_node_index(ANNOTATION_TO_EXPR_DIFFERENCE as i64)
                        .point()
                        .calculated()
                );
                return Some(Self::from_saved_link(PointLink::new(
                    link.file,
                    link.node_index + ANNOTATION_TO_EXPR_DIFFERENCE,
                )));
            }
            if n.maybe_complex()
                .is_some_and(|c| matches!(c, ComplexPoint::IndirectFinal(_)))
            {
                return Some(Self::from_type(self.as_type(i_s)).avoid_implicit_literal(i_s));
            }
        }
        None
    }

    #[inline]
    pub fn add_issue_if_deprecated<AddIssue: FnOnce(IssueKind) -> bool>(
        &self,
        db: &Database,
        on_name: Option<NodeRef>,
        add_issue: AddIssue,
    ) {
        let add_func_deprecation = |add: AddIssue, callable: &CallableContent| {
            if let Some(reason) = &callable.deprecated_reason {
                let in_node = NodeRef::from_link(db, callable.defined_at);
                if should_add_deprecated(db, in_node, on_name) {
                    return;
                }
                add(IssueKind::Deprecated {
                    identifier: format!("function {}", callable.qualified_name(db)).into(),
                    reason: reason.clone(),
                });
            }
        };
        match self.maybe_complex_point(db) {
            Some(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                add_func_deprecation(add_issue, c);
            }
            Some(ComplexPoint::FunctionOverload(overload)) => {
                if let Some(implementation) = &overload.implementation {
                    add_func_deprecation(add_issue, &implementation.callable);
                }
            }
            Some(ComplexPoint::Class(_)) => {
                if let Some(node_ref) = self.maybe_saved_node_ref(db) {
                    let class_node_ref = ClassNodeRef::from_node_ref(node_ref);
                    class_node_ref.add_issue_if_deprecated(db, on_name, add_issue);
                }
            }
            _ => (),
        }
    }

    pub fn into_proper_type(self, i_s: &InferenceState) -> Self {
        // In inferred return types of functions we don't want to return functions as such, because
        // they might refer to themselves and therefore recurse.
        if let Some(node_ref) = self.maybe_saved_node_ref(i_s.db)
            && let Some(Specific::Function) = node_ref.point().maybe_specific()
        {
            return Inferred::from_type(self.as_type(i_s));
        }
        self
    }

    pub fn into_type(self, i_s: &InferenceState) -> Type {
        if let InferredState::UnsavedComplex(ComplexPoint::TypeInstance(t)) = self.state {
            return t;
        }
        self.as_type(i_s)
    }
}

fn load_bound_method<'db: 'a, 'a, 'b>(
    i_s: &InferenceState<'db, '_>,
    instance: &'b Type,
    class: Class<'a>,
    func_link: PointLink,
) -> BoundMethod<'a, 'b> {
    let reference = NodeRef::from_link(i_s.db, func_link);
    match reference.maybe_complex() {
        Some(ComplexPoint::FunctionOverload(overload)) => {
            let func = OverloadedFunction::new(&overload.functions, Some(class));
            BoundMethod::new(instance, BoundMethodFunction::Overload(func))
        }
        None => {
            let func = Function::new(reference, Some(class));
            BoundMethod::new(instance, BoundMethodFunction::Function(func))
        }
        _ => unreachable!(),
    }
}

pub(crate) enum UnionValue<T, I: Iterator<Item = T>> {
    Single(T),
    Multiple(I),
    Any,
}

fn type_of_complex<'db: 'x, 'x>(
    i_s: &InferenceState<'db, '_>,
    complex: &'x ComplexPoint,
    definition: Option<NodeRef<'x>>,
) -> Cow<'x, Type> {
    match complex {
        ComplexPoint::Class(cls_storage) => {
            definition.unwrap().ensure_cached_class_infos(i_s);
            let class_ref = ClassNodeRef::from_node_ref(definition.unwrap());
            let cls = Class::new(
                // This can only ever happen for saved definitions, therefore we can unwrap.
                class_ref,
                cls_storage,
                Generics::NotDefinedYet { class_ref },
                None,
            );
            Cow::Owned(cls.as_type_type(i_s.db))
        }
        ComplexPoint::FunctionOverload(overload) => {
            let overload = OverloadedFunction::new(&overload.functions, i_s.current_class());
            Cow::Owned(overload.as_type(i_s, None))
        }
        ComplexPoint::TypeInstance(t) => Cow::Borrowed(t),
        ComplexPoint::TypeAlias(alias) => Cow::Owned({
            if alias.from_type_syntax {
                return Cow::Owned(i_s.db.python_state.type_alias_type_type());
            }
            if alias.is_annotated() {
                return Cow::Owned(i_s.db.python_state.typing_special_form_type());
            }
            let t = alias.type_if_valid();
            if t.is_subclassable(i_s.db) || matches!(t, Type::TypedDict(_) | Type::Any(_)) {
                Type::Type(Arc::new(alias.as_type_and_set_type_vars_any(i_s.db)))
            } else {
                i_s.db.python_state.typing_special_form_type()
            }
        }),
        ComplexPoint::TypeVarLike(t) => match t {
            TypeVarLike::TypeVar(_) => Cow::Owned(i_s.db.python_state.type_var_type()),
            TypeVarLike::TypeVarTuple(_) => Cow::Owned(i_s.db.python_state.type_var_tuple_type()),
            TypeVarLike::ParamSpec(_) => Cow::Owned(i_s.db.python_state.param_spec_type()),
        },
        ComplexPoint::NamedTupleDefinition(n) => Cow::Owned(Type::Type(n.clone())),
        ComplexPoint::TypedDictDefinition(t) => Cow::Owned(Type::Type(t.type_.clone())),
        ComplexPoint::IndirectFinal(t) => Cow::Borrowed(t),
        ComplexPoint::WidenedType(widened) => type_of_complex(i_s, &widened.original, definition),
        ComplexPoint::PyTypedMissing(_) => Cow::Borrowed(&Type::ERROR),
        ComplexPoint::HeuristicBound(b) => Cow::Borrowed(&b.type_),
        ComplexPoint::ClassInfos(_) => unreachable!("Classes are handled earlier {complex:?}"),
        ComplexPoint::TypeVarLikes(_) => unreachable!("TypeVarLikes should never be accessed"),
    }
}

fn saved_as_type<'db>(i_s: &InferenceState<'db, '_>, definition: PointLink) -> Cow<'db, Type> {
    let definition = NodeRef::from_link(i_s.db, definition);
    let point = definition.point();
    match point.kind() {
        PointKind::Specific => specific_to_type(i_s, definition, point.specific()),
        PointKind::Complex => {
            let complex = definition.file.complex_points.get(point.complex_index());
            type_of_complex(i_s, complex, Some(definition))
        }
        PointKind::FileReference => Cow::Owned(Type::Module(point.file_index())),
        x => {
            if cfg!(debug_assertions) {
                unreachable!("{x:?}")
            }
            Cow::Borrowed(&Type::ERROR)
        }
    }
}

pub fn specific_to_type<'db>(
    i_s: &InferenceState<'db, '_>,
    definition: NodeRef<'db>,
    specific: Specific,
) -> Cow<'db, Type> {
    match specific {
        Specific::AnyDueToError | Specific::InvalidTypeDefinition | Specific::BinaryExtension => {
            Cow::Borrowed(&Type::ERROR)
        }
        Specific::ModuleNotFound => Cow::Borrowed(&Type::Any(AnyCause::ModuleNotFound)),
        Specific::Cycle | Specific::UntypedFunctionSelfAssignment => {
            Cow::Borrowed(&Type::Any(AnyCause::Todo))
        }
        Specific::IntLiteral => Cow::Owned(Type::Literal(Literal {
            kind: LiteralKind::Int(definition.expect_int().parse()),
            implicit: true,
        })),
        Specific::StringLiteral => Cow::Owned(Type::Literal(Literal {
            kind: LiteralKind::String(
                DbString::from_python_string(
                    definition.file_index(),
                    definition.maybe_str().unwrap().as_python_string(),
                )
                .unwrap(),
            ),
            implicit: true,
        })),
        Specific::BoolLiteral => Cow::Owned(Type::Literal(Literal {
            kind: LiteralKind::Bool(definition.as_code() == "True"),
            implicit: true,
        })),
        Specific::BytesLiteral => Cow::Owned(Type::Literal(Literal {
            kind: LiteralKind::Bytes(DbBytes::Link(definition.as_link())),
            implicit: true,
        })),
        Specific::String => Cow::Owned(i_s.db.python_state.str_type()),
        Specific::Float => Cow::Owned(i_s.db.python_state.float_type()),
        Specific::Bytes => Cow::Owned(i_s.db.python_state.bytes_type()),
        Specific::Complex => Cow::Owned(i_s.db.python_state.complex_type()),
        Specific::Ellipsis => Cow::Owned(i_s.db.python_state.ellipsis_type()),
        Specific::Function => Cow::Owned(
            Function::new(definition, i_s.current_class()).as_type(i_s, FirstParamProperties::None),
        ),
        Specific::AnnotationOrTypeCommentSimpleClassInstance
        | Specific::AnnotationOrTypeCommentWithoutTypeVars
        | Specific::AnnotationOrTypeCommentWithTypeVars
        | Specific::AnnotationOrTypeCommentClassVar
        | Specific::AnnotationOrTypeCommentFinal => {
            use_cached_annotation_or_type_comment(i_s, definition)
        }
        Specific::MaybeSelfParam => Cow::Borrowed(&Type::Self_),
        Specific::PartialNone => {
            if definition.point().partial_flags().finished
                && definition.file.flags(i_s.db).local_partial_types
            {
                Cow::Borrowed(&i_s.db.python_state.any_or_none)
            } else {
                Cow::Borrowed(&Type::None)
            }
        }
        Specific::PartialList => {
            definition.add_need_type_annotation_issue(i_s.db, specific);
            Cow::Borrowed(&i_s.db.python_state.list_of_any)
        }
        Specific::PartialDict => {
            definition.add_need_type_annotation_issue(i_s.db, specific);
            Cow::Borrowed(&i_s.db.python_state.dict_of_any)
        }
        Specific::PartialSet => {
            definition.add_need_type_annotation_issue(i_s.db, specific);
            Cow::Borrowed(&i_s.db.python_state.set_of_any)
        }
        Specific::PartialDefaultDictWithList | Specific::PartialDefaultDictWithSet => {
            definition.add_need_type_annotation_issue(i_s.db, specific);
            Cow::Owned(new_class!(
                i_s.db.python_state.defaultdict_link(),
                Type::ERROR,
                Type::ERROR,
            ))
        }
        Specific::PartialDefaultDict => {
            definition.add_need_type_annotation_issue(i_s.db, specific);
            debug!("Warning: Tried to access a partial default dict");
            let value_node_ref = definition.add_to_node_index(NAME_DEF_TO_DEFAULTDICT_DIFF);
            Cow::Owned(new_class!(
                i_s.db.python_state.defaultdict_link(),
                Type::ERROR,
                value_node_ref.expect_complex_type().clone(),
            ))
        }
        Specific::BuiltinsIsinstance => Cow::Owned(i_s.db.python_state.isinstance_type(i_s.db)),
        Specific::BuiltinsIssubclass => Cow::Owned(i_s.db.python_state.issubclass_type(i_s.db)),
        Specific::BuiltinsSuper => Cow::Owned(i_s.db.python_state.super_type()),
        Specific::TypingTypeVarClass => {
            Cow::Owned(Type::Type(Arc::new(i_s.db.python_state.type_var_type())))
        }
        Specific::TypingTypeVarTupleClass => Cow::Owned(Type::Type(Arc::new(
            i_s.db.python_state.type_var_tuple_type(),
        ))),
        Specific::TypingParamSpecClass => {
            Cow::Owned(Type::Type(Arc::new(i_s.db.python_state.param_spec_type())))
        }
        Specific::BuiltinsType => {
            Cow::Owned(Type::Type(Arc::new(i_s.db.python_state.bare_type_type())))
        }
        Specific::TypingTuple => Cow::Borrowed(&i_s.db.python_state.type_of_arbitrary_tuple),
        Specific::CollectionsNamedTuple => Cow::Owned(
            i_s.db
                .python_state
                .collections_namedtuple_function()
                .as_type(i_s, FirstParamProperties::None),
        ),
        Specific::TypingProtocol
        | Specific::TypingGeneric
        | Specific::TypingType
        | Specific::TypingUnion
        | Specific::TypingOptional
        | Specific::TypingLiteral
        | Specific::TypingAnnotated
        | Specific::TypingNamedTuple
        | Specific::TypingTypedDict
        | Specific::TypingSelf
        | Specific::TypingClassVar
        | Specific::TypingFinal
        | Specific::TypingNeverOrNoReturn
        | Specific::TypingUnpack
        | Specific::TypingRequired
        | Specific::TypingNotRequired
        | Specific::TypingLiteralString
        | Specific::TypingTypeGuard
        | Specific::TypingTypeIs
        | Specific::TypingTypeForm
        | Specific::TypingConcatenateClass
        | Specific::TypingReadOnly
        | Specific::TypingTypeAlias
        | Specific::TypingCallable => Cow::Owned(i_s.db.python_state.typing_special_form_type()),
        // TODO (low prio) this should return the cast overload/assert_type within typeshed
        Specific::TypingCast | Specific::AssertTypeFunction => {
            Cow::Owned(i_s.db.python_state.object_type())
        }
        Specific::RevealTypeFunction => Cow::Owned(i_s.db.python_state.reveal_type(i_s.db)),
        Specific::None => Cow::Borrowed(&Type::None),
        Specific::TypingNewType => {
            Cow::Owned(Type::Type(Arc::new(i_s.db.python_state.new_type_type())))
        }
        // Typeshed defines this as object()
        Specific::TypingAny => Cow::Owned(i_s.db.python_state.object_type()),
        Specific::MypyExtensionsArg
        | Specific::MypyExtensionsDefaultArg
        | Specific::MypyExtensionsNamedArg
        | Specific::MypyExtensionsDefaultNamedArg
        | Specific::MypyExtensionsVarArg
        | Specific::MypyExtensionsKwArg => Cow::Owned(
            i_s.db
                .python_state
                .mypy_extensions_arg_func(i_s.db, specific)
                .as_type(i_s),
        ),
        Specific::MypyExtensionsFlexibleAlias => Cow::Borrowed(&Type::Any(AnyCause::Internal)),
        // TODO dataclass transforms should probably be handled properly
        Specific::TypingDataclassTransform => Cow::Owned(i_s.db.python_state.function_type()),
        Specific::TypingTypeAliasType => Cow::Owned(Type::Type(Arc::new(
            i_s.db.python_state.type_alias_type_type(),
        ))),
        Specific::BuiltinsSentinel => {
            Cow::Owned(Type::Type(Arc::new(i_s.db.python_state.sentinel_type())))
        }
        actual => {
            recoverable_error!("Wanted to make invalid Specific to a type: {actual:?}");
            Cow::Borrowed(&Type::ERROR)
        }
    }
}

pub fn add_attribute_error(
    i_s: &InferenceState,
    node_ref: NodeRef,
    full_type: &Type,
    t: &Type,
    name: &str,
) {
    let object = match t {
        Type::Module(_) => {
            if !node_ref.file.flags(i_s.db).ignore_missing_imports {
                node_ref.add_issue(i_s, IssueKind::ModuleAttributeError { name: name.into() });
            }
            return;
        }
        _ => format!("\"{}\"", t.format_short(i_s.db)).into(),
    };
    let name = Box::from(name);
    if let Type::TypeVar(usage) = full_type
        && let TypeVarKind::Bound(bound) = usage.type_var.kind(i_s.db)
        && bound.is_union_like(i_s.db)
    {
        let bound = bound.format_short(i_s.db);
        let type_var_name = usage.type_var.name(i_s.db);
        node_ref.add_issue(
            i_s,
            IssueKind::UnionAttributeErrorOfUpperBound(format!(
                r#"Item {object} of the upper bound "{bound}" of type variable "{type_var_name}" has no attribute "{name}""#
            ).into())
        );
        return;
    }
    node_ref.add_issue(
        i_s,
        match full_type.is_union_like(i_s.db) {
            false => IssueKind::AttributeError { object, name },
            true => IssueKind::UnionAttributeError {
                object,
                union: full_type.format_short(i_s.db),
                name,
            },
        },
    );
}
