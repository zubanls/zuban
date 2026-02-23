use std::{borrow::Cow, cell::RefCell, sync::Arc};

use num_bigint::BigInt;
use parsa_python_cst::{NodeIndex, ParamKind};
use vfs::FileIndex;

use crate::{
    arguments::{Args, CombinedArgs, KnownArgs, KnownArgsWithCustomAddIssue},
    database::{
        ComplexPoint, Database, Locality, OverloadDefinition, Point, PointKind, PointLink, Specific,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        ANNOTATION_TO_EXPR_DIFFERENCE, ClassNodeRef, PythonFile, maybe_saved_annotation,
        on_argument_type_error, should_add_deprecated, use_cached_annotation_or_type_comment,
    },
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    matching::{
        ErrorStrs, Generics, IteratorContent, LookupKind, Matcher, OnLookupError, OnTypeError,
        calculate_property_return, create_signature_without_self_for_callable, match_self_type,
        maybe_class_usage, maybe_replace_class_type_vars, replace_class_type_vars,
    },
    new_class,
    node_ref::NodeRef,
    recoverable_error,
    result_context::ResultContext,
    type_::{
        AnyCause, CallableContent, CallableLike, CallableParams, ClassGenerics, DbBytes, DbString,
        FunctionKind, FunctionOverload, GenericClass, GenericItem, GenericsList, IterCause,
        IterInfos, Literal as DbLiteral, LiteralKind, LiteralValue, LookupResult, NeverCause,
        PropertySetter, PropertySetterType, ReplaceTypeVarLikes, Type, TypeVarKind, TypeVarLike,
        TypeVarLikes, execute_tuple_class, execute_type_of_type, merge_class_type_vars,
    },
    type_helpers::{
        BoundMethod, BoundMethodFunction, Callable, Class, FirstParamProperties, FuncLike as _,
        Function, Instance, LookupDetails, OverloadedFunction, TypeOrClass, execute_assert_type,
        execute_cast, execute_isinstance, execute_issubclass, execute_reveal_type, execute_super,
    },
};

pub const NAME_DEF_TO_DEFAULTDICT_DIFF: i64 = -1;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub(crate) struct MroIndex(pub u32);

impl From<usize> for MroIndex {
    fn from(item: usize) -> Self {
        Self(item as u32)
    }
}

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
pub struct BoundMethodState {
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

    fn new_bound_method(instance: Type, mro_index: MroIndex, func_link: PointLink) -> Self {
        Self {
            state: InferredState::BoundMethod(BoundMethodState {
                instance,
                mro_index,
                func_link,
            }),
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

    pub fn new_any_from_error() -> Self {
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

    pub fn from_type(t: Type) -> Self {
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

    fn load_bound_method_class<'a: 'slf>(
        i_s: &InferenceState<'db, 'a>,
        instance: &'slf Type,
        mro_index: MroIndex,
    ) -> Class<'slf> {
        let Some(instance_class) = instance.inner_generic_class(i_s) else {
            unreachable!("{instance:?}")
        };
        let Some((_, class_t)) = instance_class.mro(i_s.db).nth(mro_index.0 as usize) else {
            // Happens with super().__init__ when self: SomeProtocol.
            return i_s.db.python_state.object_class();
        };

        // Mro classes are never owned, because they are saved on classes.
        match class_t {
            TypeOrClass::Class(class) => class,
            TypeOrClass::Type(t) => match t {
                Cow::Borrowed(Type::Dataclass(d)) => d.class(i_s.db),
                _ => unreachable!("{t:?}"),
            },
        }
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
                GenericItem::TypeArg(Type::Any(AnyCause::UnknownTypeParam))
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
    ) -> UnionValue<DbLiteral, impl Iterator<Item = DbLiteral> + 'slf> {
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
                    return UnionValue::Single(DbLiteral {
                        kind: LiteralKind::Int(node_ref.expect_int().parse()),
                        implicit: true,
                    });
                }
                Some(Specific::StringLiteral) => {
                    return UnionValue::Single(DbLiteral {
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
        let infer = |i_s: &InferenceState, literal: DbLiteral| {
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
            UnionValue::Multiple(mut literals) => literals
                .next()
                .and_then(|l| infer(i_s, l))
                .and_then(|mut inferred| {
                    for literal in literals {
                        if let Some(new_inf) = infer(i_s, literal) {
                            inferred = inferred.simplified_union(i_s, new_inf);
                        } else {
                            return None;
                        }
                    }
                    Some(inferred)
                }),
            UnionValue::Any => None,
        }
    }

    pub fn run_on_str_literals(
        &self,
        i_s: &InferenceState,
        callable: impl Fn(&str) -> Option<Inferred>,
    ) -> Option<Inferred> {
        let infer = |i_s: &InferenceState, literal: DbLiteral| {
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
            UnionValue::Multiple(mut literals) => literals
                .next()
                .and_then(|l| infer(i_s, l))
                .and_then(|mut inferred| {
                    for literal in literals {
                        if let Some(new_inf) = infer(i_s, literal) {
                            inferred = inferred.simplified_union(i_s, new_inf);
                        } else {
                            return None;
                        }
                    }
                    Some(inferred)
                }),
            UnionValue::Any => None,
        }
    }

    pub fn maybe_bool_literal(&self, i_s: &InferenceState) -> Option<bool> {
        if let Type::Literal(DbLiteral {
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
        if let Type::Literal(DbLiteral {
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
                            "Why overwrite? New: {:?} Previous: {node_ref:?} line {}",
                            self.debug_info(i_s.db),
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
        match self.avoid_implicit_literal_cow(i_s) {
            Cow::Borrowed(_) => self,
            Cow::Owned(owned) => owned,
        }
    }

    pub fn avoid_implicit_literal_cow(&self, i_s: &InferenceState) -> Cow<'_, Self> {
        if i_s.is_calculating_enum_members() {
            return Cow::Borrowed(self);
        }
        match self.state {
            InferredState::Saved(link) => {
                let node_ref = NodeRef::from_link(i_s.db, link);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::MaybeSelfParam => {
                            return Cow::Owned(Inferred::from_type(i_s.current_type().unwrap()));
                        }
                        Specific::IntLiteral
                        | Specific::StringLiteral
                        | Specific::BytesLiteral
                        | Specific::BoolLiteral
                        | Specific::AnnotationOrTypeCommentFinal => (),
                        _ => return Cow::Borrowed(self),
                    },
                    PointKind::Complex => {
                        if node_ref.maybe_complex().unwrap().maybe_instance().is_none() {
                            return Cow::Borrowed(self);
                        }
                    }
                    _ => return Cow::Borrowed(self),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(_)) => (),
            _ => return Cow::Borrowed(self),
        }
        if let Some(t) = self.as_cow_type(i_s).maybe_avoid_implicit_literal(i_s.db) {
            Cow::Owned(Self::from_type(t))
        } else {
            Cow::Borrowed(self)
        }
    }

    #[inline]
    pub fn gather_simplified_union(
        i_s: &InferenceState,
        callable: impl FnOnce(&mut dyn FnMut(Self)),
    ) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |inferred| {
            *r = Some(match r.take() {
                Some(i) => i.simplified_union(i_s, inferred),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| Inferred::new_never(NeverCause::Other))
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

    pub(crate) fn bind_instance_descriptors(
        self,
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        func_class: Class,
        add_issue: impl Fn(IssueKind),
        mro_index: MroIndex,
        disallow_lazy_bound_method: bool,
        avoid_inferring_return_types: bool,
    ) -> Option<(Self, AttributeKind)> {
        self.bind_instance_descriptors_internal(
            i_s,
            for_name,
            instance,
            func_class,
            add_issue,
            mro_index,
            ApplyDescriptorsKind::All,
            disallow_lazy_bound_method,
            avoid_inferring_return_types,
        )
    }

    fn bind_instance_descriptors_internal(
        self,
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        attribute_class: Class,
        add_issue: impl Fn(IssueKind),
        mro_index: MroIndex,
        apply_descriptors_kind: ApplyDescriptorsKind,
        disallow_lazy_bound_method: bool,
        avoid_inferring_return_types: bool,
    ) -> Option<(Self, AttributeKind)> {
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::Function => {
                            let func = prepare_func(i_s, *definition, attribute_class);
                            let attr_kind = AttributeKind::DefMethod { is_final: false };
                            if !func.node().params().iter().next().is_some_and(|p| {
                                matches!(
                                    p.kind(),
                                    ParamKind::PositionalOnly
                                        | ParamKind::PositionalOrKeyword
                                        | ParamKind::Star
                                )
                            }) {
                                add_issue(IssueKind::NotAcceptingSelfArgument {
                                    function_name: Box::from(func.name()),
                                    callable: func
                                        .as_callable(i_s, FirstParamProperties::None)
                                        .format(&FormatData::new_short(i_s.db))
                                        .into(),
                                })
                            }
                            return if let Some(first_type) = func.first_param_annotation_type(i_s) {
                                Some((
                                    infer_callable_with_first_param_annotation(
                                        i_s,
                                        func,
                                        &first_type,
                                        &attribute_class,
                                        instance,
                                        add_issue,
                                    ),
                                    attr_kind,
                                ))
                            } else if avoid_inferring_return_types {
                                Some((
                                    Self::from_type(
                                        BoundMethod::new(
                                            &instance,
                                            BoundMethodFunction::Function(func),
                                        )
                                        .as_type_without_inferring_returns(i_s),
                                    ),
                                    attr_kind,
                                ))
                            } else if disallow_lazy_bound_method {
                                Some((
                                    Self::from_type(
                                        BoundMethod::new(
                                            &instance,
                                            BoundMethodFunction::Function(func),
                                        )
                                        .as_type(i_s),
                                    ),
                                    attr_kind,
                                ))
                            } else {
                                Some((
                                    Self::new_bound_method(instance, mro_index, *definition),
                                    attr_kind,
                                ))
                            };
                        }
                        specific if specific.is_annotation_or_type_comment() => {
                            let t = use_cached_annotation_or_type_comment(i_s, node_ref);
                            let is_remapped = matches!(
                                specific,
                                Specific::AnnotationOrTypeCommentWithTypeVars
                                | Specific::AnnotationOrTypeCommentFinal
                                if !attribute_class.needs_generic_remapping_for_attributes(i_s, &t)
                            );
                            let t = if is_remapped {
                                replace_class_type_vars(i_s.db, &t, &attribute_class, &|| {
                                    Some(instance.clone())
                                })
                            } else {
                                Cow::Borrowed(t.as_ref())
                            };
                            let is_class_var =
                                specific == Specific::AnnotationOrTypeCommentClassVar;
                            let attr_kind = if is_class_var {
                                AttributeKind::ClassVar
                            } else if specific == Specific::AnnotationOrTypeCommentFinal {
                                AttributeKind::Final
                            } else {
                                AttributeKind::AnnotatedAttribute
                            };
                            if let Some(r) = Self::bind_instance_descriptors_for_type(
                                i_s,
                                for_name,
                                instance,
                                attribute_class,
                                add_issue,
                                &t,
                                if is_class_var {
                                    ApplyDescriptorsKind::All
                                } else {
                                    ApplyDescriptorsKind::NoBoundMethod
                                },
                                avoid_inferring_return_types,
                            ) {
                                return r.map(|(inf, _)| (inf, attr_kind));
                            }
                            if is_remapped {
                                return Some((Inferred::from_type(t.into_owned()), attr_kind));
                            }
                            return Some((self, attr_kind));
                        }
                        Specific::PartialNone if i_s.db.project.flags.local_partial_types => {
                            // Looking up partials means that they have not yet been processed and
                            // will be inferred as None | Any. I'm not 100% sure this is always
                            // safe, but at this point we haven't found code that
                            return Some((
                                Inferred::from_type(i_s.db.python_state.any_or_none.clone()),
                                AttributeKind::Attribute,
                            ));
                        }
                        _ => (),
                    },
                    PointKind::Complex => {
                        match node_ref.maybe_complex().unwrap() {
                            ComplexPoint::FunctionOverload(o) => {
                                if i_s.db.project.flags.disallow_deprecated
                                    && let Some(i) = &o.implementation
                                    && let Some(reason) = &i.callable.deprecated_reason
                                    && !matches!(i.callable.kind, FunctionKind::Staticmethod)
                                {
                                    add_issue(IssueKind::Deprecated {
                                        identifier: format!(
                                            "function {}",
                                            i.callable.qualified_name(i_s.db)
                                        )
                                        .into(),
                                        reason: reason.clone(),
                                    });
                                }
                                let kind = o.kind();
                                let attr_kind = match kind {
                                    FunctionKind::Staticmethod => {
                                        return Some((
                                            self,
                                            AttributeKind::Staticmethod {
                                                is_final: o.is_final,
                                            },
                                        ));
                                    }
                                    FunctionKind::Function { .. } => AttributeKind::DefMethod {
                                        is_final: o.is_final,
                                    },
                                    FunctionKind::Classmethod { .. } => {
                                        AttributeKind::Classmethod {
                                            is_final: o.is_final,
                                        }
                                    }
                                    FunctionKind::Property { .. } => unreachable!(),
                                };

                                let has_self_arguments = o
                                    .iter_functions()
                                    .any(|c| c.kind.had_first_self_or_class_annotation());
                                if has_self_arguments {
                                    let results: Vec<_> = o
                                        .iter_functions()
                                        .filter_map(|callable| {
                                            match kind {
                                                FunctionKind::Function { .. } => {
                                                    if let Some(t) =
                                                        callable.first_positional_type()
                                                    {
                                                        create_signature_without_self_for_callable(
                                                            i_s,
                                                            callable,
                                                            &instance,
                                                            &attribute_class,
                                                            &t,
                                                        )
                                                    } else {
                                                        None
                                                    }
                                                }
                                                FunctionKind::Classmethod { .. } => {
                                                    infer_class_method_on_instance(
                                                        i_s,
                                                        &instance,
                                                        attribute_class,
                                                        callable,
                                                    )
                                                }
                                                FunctionKind::Staticmethod
                                                | FunctionKind::Property { .. } => unreachable!(),
                                            }
                                            .map(Arc::new)
                                        })
                                        .collect();
                                    match results.len() {
                                        0 => {
                                            let overload = OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            );
                                            let t = IssueKind::InvalidClassMethodFirstArgument {
                                                argument_type: Type::Type(Arc::new(instance))
                                                    .format_short(i_s.db),
                                                function_name: Box::from(overload.name(i_s.db)),
                                                // Mypy just picks the first function.
                                                callable: o
                                                    .functions
                                                    .iter_functions()
                                                    .next()
                                                    .unwrap()
                                                    .format(&FormatData::new_short(i_s.db))
                                                    .into(),
                                            };
                                            add_issue(t);
                                            return Some((Self::new_any_from_error(), attr_kind));
                                        }
                                        1 => {
                                            return Some((
                                                Inferred::from_type(Type::Callable(
                                                    results.into_iter().next().unwrap(),
                                                )),
                                                attr_kind,
                                            ));
                                        }
                                        _ => {
                                            return Some((
                                                Inferred::from_type(Type::FunctionOverload(
                                                    FunctionOverload::new(
                                                        results.into_iter().collect(),
                                                    ),
                                                )),
                                                attr_kind,
                                            ));
                                        }
                                    }
                                }
                                return Some((
                                    if disallow_lazy_bound_method {
                                        Self::from_type(
                                            OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            )
                                            .as_type(i_s, Some(&|| instance.clone())),
                                        )
                                    } else {
                                        Self::new_bound_method(instance, mro_index, *definition)
                                    },
                                    attr_kind,
                                ));
                            }
                            ComplexPoint::TypeInstance(t) => {
                                if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                    i_s,
                                    for_name,
                                    instance,
                                    attribute_class,
                                    add_issue,
                                    t,
                                    apply_descriptors_kind,
                                    avoid_inferring_return_types,
                                ) {
                                    return inf;
                                }
                            }
                            ComplexPoint::WidenedType(widened) => {
                                if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                    i_s,
                                    for_name,
                                    instance,
                                    attribute_class,
                                    add_issue,
                                    &widened.widened,
                                    apply_descriptors_kind,
                                    avoid_inferring_return_types,
                                ) {
                                    return inf;
                                } else {
                                    return Some((
                                        Inferred::from_type(widened.widened.clone()),
                                        AttributeKind::Attribute,
                                    ));
                                }
                            }
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex
                    && let Some(inf) = Self::bind_instance_descriptors_for_type(
                        i_s,
                        for_name,
                        instance,
                        attribute_class,
                        add_issue,
                        t,
                        apply_descriptors_kind,
                        avoid_inferring_return_types,
                    )
                {
                    return inf;
                }
            }
            InferredState::UnsavedFileReference(_)
            | InferredState::UnsavedSpecific(_)
            | InferredState::BoundMethod { .. } => (),
        }
        Some((self, AttributeKind::Attribute))
    }

    fn bind_instance_descriptors_for_type(
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        attribute_class: Class,
        add_issue: impl Fn(IssueKind),
        t: &Type,
        apply_descriptors_kind: ApplyDescriptorsKind,
        avoid_inferring_return_types: bool,
    ) -> Option<Option<(Self, AttributeKind)>> {
        let mut t = t; // Weird lifetime issue
        let add_invalid_self_arg = |c: &CallableContent| {
            add_issue(IssueKind::InvalidSelfArgument {
                argument_type: instance.format_short(i_s.db),
                function_name: Box::from(
                    c.name
                        .as_ref()
                        .map(|n| n.as_str(i_s.db))
                        .unwrap_or(for_name),
                ),
                callable: c.format(&FormatData::new_short(i_s.db)).into(),
            })
        };
        match t {
            Type::Callable(c) => {
                if i_s.db.project.flags.disallow_deprecated
                    && let Some(reason) = &c.deprecated_reason
                {
                    add_issue(IssueKind::Deprecated {
                        identifier: format!("function {}", c.qualified_name(i_s.db)).into(),
                        reason: reason.clone(),
                    });
                    return Self::bind_instance_descriptors_for_type(
                        i_s,
                        for_name,
                        instance,
                        attribute_class,
                        add_issue,
                        &Type::Callable(c.remove_deprecated_reason()),
                        apply_descriptors_kind,
                        avoid_inferring_return_types,
                    );
                }
                match &c.kind {
                    FunctionKind::Function { .. }
                        if !i_s.db.mypy_compatible()
                            // ParamSpecs are bound and can only be used from self
                            && c.params.maybe_param_spec().is_none()
                            && attribute_class.maybe_dataclass(i_s.db).is_none()
                            || !matches!(
                                apply_descriptors_kind,
                                ApplyDescriptorsKind::NoBoundMethod
                            ) =>
                    {
                        debug_assert!(matches!(c.kind, FunctionKind::Function { .. }));
                        if let Some(f) = c.first_positional_type() {
                            let mut new_c = create_signature_without_self_for_callable(
                                i_s,
                                c,
                                &instance,
                                &attribute_class,
                                &f,
                            )
                            .map(Arc::new)
                            .unwrap_or_else(|| {
                                add_invalid_self_arg(c);
                                i_s.db.python_state.any_callable_from_error.clone()
                            });
                            if avoid_inferring_return_types
                                && let Some(func) = new_c.maybe_original_function(i_s.db)
                                && func.return_annotation().is_none()
                            {
                                let mut new = new_c.as_ref().clone();
                                new.return_type = Type::Any(AnyCause::Unannotated);
                                new_c = Arc::new(new)
                            }
                            return Some(Some((
                                Inferred::from_type(Type::Callable(new_c)),
                                AttributeKind::DefMethod {
                                    is_final: c.is_final,
                                },
                            )));
                        } else {
                            add_issue(IssueKind::NotAcceptingSelfArgument {
                                function_name: Box::from(for_name),
                                callable: c.format(&FormatData::new_short(i_s.db)).into(),
                            })
                        }
                    }
                    FunctionKind::Function { .. } => (),
                    FunctionKind::Property { setter_type, .. } => {
                        return Some(Some(
                            if let Some(t) = calculate_property_return(
                                i_s,
                                &instance,
                                &attribute_class,
                                c,
                                avoid_inferring_return_types,
                            ) {
                                let setter_type = setter_type.as_ref().map(|s| match &s.type_ {
                                    PropertySetterType::OtherType(t)
                                        if attribute_class
                                            .needs_generic_remapping_for_attributes(i_s, t) =>
                                    {
                                        let t = replace_class_type_vars(
                                            i_s.db,
                                            t,
                                            &attribute_class,
                                            &|| Some(instance.clone()),
                                        );
                                        Arc::new(PropertySetter {
                                            type_: PropertySetterType::OtherType(t.into_owned()),
                                            deprecated_reason: None,
                                        })
                                    }
                                    _ => s.clone(),
                                });
                                (
                                    Inferred::from_type(t),
                                    AttributeKind::Property {
                                        setter_type,
                                        is_abstract: c.is_abstract,
                                        is_final: c.is_final,
                                    },
                                )
                            } else {
                                add_invalid_self_arg(c);
                                (Inferred::new_any_from_error(), AttributeKind::Attribute)
                            },
                        ));
                    }
                    FunctionKind::Classmethod { .. } => {
                        let result =
                            infer_class_method_on_instance(i_s, &instance, attribute_class, c);
                        if result.is_none() {
                            let t = IssueKind::InvalidClassMethodFirstArgument {
                                argument_type: Type::Type(Arc::new(instance)).format_short(i_s.db),
                                function_name: c.name(i_s.db).into(),
                                callable: t.format_short(i_s.db),
                            };
                            add_issue(t);
                            return Some(Some((
                                Self::new_any_from_error(),
                                AttributeKind::Attribute,
                            )));
                        }
                        let is_final = c.is_final;
                        return Some(result.map(|mut c| {
                            if avoid_inferring_return_types
                                && let Some(func) = c.maybe_original_function(i_s.db)
                                && func.return_annotation().is_none()
                            {
                                c.return_type = Type::Any(AnyCause::Unannotated);
                            }
                            (
                                callable_into_inferred(c),
                                AttributeKind::Classmethod { is_final },
                            )
                        }));
                    }
                    FunctionKind::Staticmethod => {
                        let mut t = t.clone();
                        if avoid_inferring_return_types
                            && let Some(func) = c.maybe_original_function(i_s.db)
                            && func.return_annotation().is_none()
                            && let Type::Callable(c) = &t
                        {
                            let mut new_c = c.as_ref().clone();
                            new_c.return_type = Type::Any(AnyCause::Unannotated);
                            t = Type::Callable(Arc::new(new_c));
                        }
                        return Some(Some((
                            Inferred::from_type(t),
                            AttributeKind::Staticmethod {
                                is_final: c.is_final,
                            },
                        )));
                    }
                }
            }
            Type::CustomBehavior(custom) => {
                return Some(Some((
                    Inferred::from_type(Type::CustomBehavior(custom.bind(Arc::new(instance)))),
                    AttributeKind::DefMethod { is_final: false },
                )));
            }
            _ => (),
        }

        let mut new = None;
        if attribute_class.needs_generic_remapping_for_attributes(i_s, t) {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| Some(instance.clone()),
            ));
            t = new.as_ref().unwrap();
        }

        if let Type::Class(c) = t {
            let class_ref = ClassNodeRef::from_link(i_s.db, c.link);
            let potential_descriptor = use_instance_with_ref(
                class_ref,
                Generics::from_class_generics(i_s.db, class_ref, &c.generics),
                None,
            );
            if let Some(inf) = potential_descriptor.bind_dunder_get(i_s, add_issue, instance) {
                return Some(Some((inf, AttributeKind::Attribute)));
            }
        }
        // TODO this clone should not be necessary, but there appears to be a bug in the compiler.
        if let Some(new) = new.clone() {
            return Some(Some((
                Inferred::from_type(new.into_owned()),
                AttributeKind::Attribute,
            )));
        }
        None
    }

    pub(crate) fn bind_class_descriptors(
        self,
        i_s: &InferenceState,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        func_class_type: &TypeOrClass,
        add_issue: impl Fn(IssueKind),
        apply_descriptors: ApplyClassDescriptorsOrigin,
        as_type_type: Option<&dyn Fn() -> Type>,
    ) -> Option<(Self, AttributeKind)> {
        let mut attr_kind = AttributeKind::Attribute;
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::Function => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            let c = func.as_callable(i_s, FirstParamProperties::None);
                            let c = Arc::new(merge_class_type_vars(
                                i_s.db,
                                &c,
                                *class,
                                attribute_class,
                                func_class_type,
                            ));
                            return Some((
                                Inferred::from_type(Type::Callable(c)),
                                AttributeKind::DefMethod { is_final: false },
                            ));
                        }
                        specific @ (Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentFinal) => {
                            if specific == Specific::AnnotationOrTypeCommentWithTypeVars
                                && apply_descriptors.should_add_ambigous_class_var_access()
                            {
                                add_issue(IssueKind::AmbigousClassVariableAccess);
                            }
                            let t = use_cached_annotation_or_type_comment(
                                i_s,
                                NodeRef::from_link(i_s.db, *definition),
                            );
                            if specific == Specific::AnnotationOrTypeCommentClassVar {
                                attr_kind = AttributeKind::ClassVar
                            } else if specific == Specific::AnnotationOrTypeCommentFinal {
                                attr_kind = AttributeKind::Final
                            } else {
                                attr_kind = AttributeKind::AnnotatedAttribute
                            };
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                &t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        _ => (),
                    },
                    PointKind::Complex => match node_ref.maybe_complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => match o.kind() {
                            FunctionKind::Function { .. } => {
                                return Some((
                                    Inferred::from_type(Type::FunctionOverload(
                                        FunctionOverload::new(
                                            o.iter_functions()
                                                .map(|c| {
                                                    Arc::new(merge_class_type_vars(
                                                        i_s.db,
                                                        c,
                                                        *class,
                                                        attribute_class,
                                                        func_class_type,
                                                    ))
                                                })
                                                .collect(),
                                        ),
                                    )),
                                    AttributeKind::Attribute,
                                ));
                            }
                            FunctionKind::Property { .. } => unreachable!(),
                            FunctionKind::Classmethod { .. } => {
                                let Some(inf) =
                                    infer_overloaded_class_method(i_s, *class, attribute_class, o)
                                else {
                                    add_issue(IssueKind::InvalidSelfArgument {
                                        argument_type: class
                                            .as_type_type(i_s.db)
                                            .format_short(i_s.db),
                                        function_name: o
                                            .iter_functions()
                                            .next()
                                            .map(|c| c.name(i_s.db))
                                            .unwrap()
                                            .into(),
                                        callable: self.format_short(i_s),
                                    });
                                    return Some((
                                        Inferred::new_any_from_error(),
                                        AttributeKind::Attribute,
                                    ));
                                };
                                return Some((inf, AttributeKind::Attribute));
                            }
                            FunctionKind::Staticmethod => (),
                        },
                        ComplexPoint::TypeInstance(t) => {
                            if let Type::Callable(c) = t {
                                match c.kind {
                                    FunctionKind::Function { .. } => {
                                        attr_kind = AttributeKind::DefMethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                    FunctionKind::Property { .. } => (),
                                    FunctionKind::Classmethod { .. } => {
                                        attr_kind = AttributeKind::Classmethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                    FunctionKind::Staticmethod => {
                                        attr_kind = AttributeKind::Staticmethod {
                                            is_final: c.is_final,
                                        };
                                    }
                                }
                            }
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        ComplexPoint::IndirectFinal(t) => {
                            attr_kind = AttributeKind::Final;
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                t,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        ComplexPoint::WidenedType(widened) => {
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                add_issue,
                                apply_descriptors,
                                &widened.widened,
                                as_type_type,
                                func_class_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            } else {
                                return Some((
                                    Inferred::from_type(widened.widened.clone()),
                                    attr_kind,
                                ));
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex
                    && let Some(inf) = Self::bind_class_descriptors_for_type(
                        i_s,
                        class,
                        attribute_class,
                        add_issue,
                        apply_descriptors,
                        t,
                        as_type_type,
                        func_class_type,
                    )
                {
                    return inf.map(|inf| (inf, AttributeKind::Attribute));
                }
            }
            InferredState::UnsavedFileReference(_)
            | InferredState::UnsavedSpecific(_)
            | InferredState::BoundMethod { .. } => (),
        }
        Some((self, attr_kind))
    }

    pub(crate) fn bind_class_descriptors_for_type(
        i_s: &InferenceState,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        add_issue: impl Fn(IssueKind),
        apply_descriptors: ApplyClassDescriptorsOrigin,
        t: &Type,
        as_type_type: Option<&dyn Fn() -> Type>,
        func_class_type: &TypeOrClass,
    ) -> Option<Option<Self>> {
        let mut t = t;
        if let Type::Callable(c) = t {
            if i_s.db.project.flags.disallow_deprecated
                && let Some(reason) = &c.deprecated_reason
            {
                add_issue(IssueKind::Deprecated {
                    identifier: format!("function {}", c.qualified_name(i_s.db)).into(),
                    reason: reason.clone(),
                });
                return Self::bind_class_descriptors_for_type(
                    i_s,
                    class,
                    attribute_class,
                    add_issue,
                    apply_descriptors,
                    &Type::Callable(c.remove_deprecated_reason()),
                    as_type_type,
                    func_class_type,
                );
            }
            match c.kind {
                FunctionKind::Function { .. } => {
                    return Some(Some(Inferred::from_type(Type::Callable(Arc::new(
                        merge_class_type_vars(i_s.db, c, *class, attribute_class, func_class_type),
                    )))));
                }
                FunctionKind::Property { .. } => {
                    if apply_descriptors.should_apply() {
                        return Some(Some(Inferred::from_type(
                            i_s.db.python_state.property_type(),
                        )));
                    }
                }
                FunctionKind::Classmethod { .. } => {
                    let result = infer_class_method(i_s, *class, attribute_class, c, as_type_type);
                    if result.is_none() {
                        let inv = IssueKind::InvalidSelfArgument {
                            argument_type: class.as_type_type(i_s.db).format_short(i_s.db),
                            function_name: c.name(i_s.db).into(),
                            callable: t.format_short(i_s.db),
                        };
                        add_issue(inv);
                        return Some(Some(Self::new_any_from_error()));
                    }
                    return Some(result.map(callable_into_inferred));
                }
                FunctionKind::Staticmethod => (),
            }
        }
        let mut new = None;
        if attribute_class.needs_generic_remapping_for_attributes(i_s, t) {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| {
                    Some({
                        if let Some(as_type_type) = as_type_type {
                            let Type::Type(t) = as_type_type() else {
                                unreachable!()
                            };
                            (*t).clone()
                        } else {
                            class.as_type(i_s.db)
                        }
                    })
                },
            ));
            t = new.as_ref().unwrap();
        }

        if let Type::Class(c) = t
            && apply_descriptors.should_apply()
        {
            let class_ref = ClassNodeRef::from_link(i_s.db, c.link);
            let inst = use_instance_with_ref(
                class_ref,
                Generics::from_class_generics(i_s.db, class_ref, &c.generics),
                None,
            );
            if let Some(inf) = inst
                .type_lookup(i_s, &add_issue, "__get__")
                .into_maybe_inferred()
            {
                let class_as_inferred = class.as_inferred(i_s);
                return Some(Some(inf.execute(
                    i_s,
                    &CombinedArgs::new(
                        &KnownArgsWithCustomAddIssue::new(&Inferred::new_none(), &add_issue),
                        &KnownArgsWithCustomAddIssue::new(&class_as_inferred, &add_issue),
                    ),
                )));
            }
        }
        // TODO this clone should not be necessary, but there appears to be a bug in the compiler.
        if let Some(new) = new.clone() {
            return Some(Some(Inferred::from_type(new.into_owned())));
        }
        None
    }

    pub fn bind_new_descriptors(
        self,
        i_s: &InferenceState,
        class: &Class,
        class_of_attribute: Option<Class>,
        add_issue: &dyn Fn(IssueKind),
    ) -> Self {
        // This method exists for __new__
        let attribute_class = class_of_attribute.unwrap_or(*class);
        let to_class_method = |callable| {
            let result = infer_class_method(
                i_s,
                *class,
                attribute_class,
                callable,
                Some(&|| class.as_type_type(i_s.db)),
            );
            if result.is_none()
                && let Some(t) = callable.first_positional_type()
            {
                let class_t = class.as_type_type(i_s.db);
                add_issue(IssueKind::InvalidSelfArgument {
                    argument_type: class_t.format_short(i_s.db),
                    function_name: "__new__".into(),
                    callable: t.format_short(i_s.db),
                })
            }
            result
        };
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => {
                        if point.specific() == Specific::Function {
                            let func = Function::new(node_ref, Some(attribute_class));
                            if let Some(result) =
                                to_class_method(&func.as_callable(i_s, FirstParamProperties::None))
                            {
                                return callable_into_inferred(result);
                            } else {
                                // e.g. def __new__() -> X: ...
                                // Error will be added to the class and not the caller
                                return Self::new_any_from_error();
                            }
                        }
                    }
                    PointKind::Complex => match node_ref.maybe_complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => {
                            let Some(inf) =
                                infer_overloaded_class_method(i_s, *class, attribute_class, o)
                            else {
                                return Self::new_any_from_error();
                            };
                            return inf;
                        }
                        complex => {
                            if let Some(Type::Callable(c)) = complex.maybe_instance() {
                                let Some(c) = to_class_method(c) else {
                                    return Self::new_any_from_error();
                                };
                                return Inferred::from_type(Type::Callable(Arc::new(c)));
                            }
                        }
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                // This is reached by NamedTuples. Not sure it this reached otherwise as well.
                let result = to_class_method(c);
                if let Some(result) = result {
                    return callable_into_inferred(result);
                } else {
                    return Self::new_any_from_error();
                }
            }
            _ => (),
        }
        self
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
            | Specific::PyTypedMissing => Some(AnyCause::FromError),
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
        add_issue: &dyn Fn(IssueKind),
        callable: &mut impl FnMut(&Type, LookupDetails),
    ) {
        self.as_cow_type(i_s).run_after_lookup_on_each_union_member(
            i_s,
            Some(self),
            in_file,
            name,
            kind,
            &mut ResultContext::ValueExpected,
            add_issue,
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
        add_issue: &dyn Fn(IssueKind),
        on_lookup_error: OnLookupError,
        on_type_error: OnTypeError,
    ) -> Self {
        let mut result: Option<Inferred> = None;
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
                result = if let Some(r) = result.take() {
                    Some(r.simplified_union(i_s, inf))
                } else {
                    Some(inf)
                }
            },
        );
        result.unwrap_or_else(|| Self::new_never(NeverCause::Other))
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
                                    let n = NodeRef::from_link(i_s.db, *assignment_definition);
                                    return n
                                        .file
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
                                    let n = NodeRef::from_link(i_s.db, *assignment_definition);
                                    return n
                                        .file
                                        .name_resolution_for_types(i_s)
                                        .compute_special_alias_assignment(
                                            specific,
                                            n.expect_assignment(),
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
                                    let n = NodeRef::from_link(i_s.db, *assignment_definition);
                                    if let Some(inf) = n
                                        .file
                                        .name_resolution_for_types(i_s)
                                        .execute_type_alias_from_type_alias_type(
                                            args,
                                            n.expect_assignment(),
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
                                debug!("Execute type definition with {}", stringify!($name));
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
                                            IssueKind::MissingTypeParameters {
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
                    | Specific::TypingNamedTuple
                    | Specific::CollectionsNamedTuple
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
                )
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
                from.add_issue(i_s, type_)
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
    pub fn add_issue_if_deprecated<AddIssue: FnOnce(IssueKind)>(
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

fn use_instance_with_ref<'a>(
    class_reference: ClassNodeRef<'a>,
    generics: Generics<'a>,
    instance_reference: Option<&'a Inferred>,
) -> Instance<'a> {
    let class = Class::from_position(class_reference, generics, None);
    Instance::new(class, instance_reference)
}

fn prepare_func<'db, 'class>(
    i_s: &InferenceState<'db, '_>,
    definition: PointLink,
    func_class: Class<'class>,
) -> Function<'db, 'class> {
    let node_ref = NodeRef::from_link(i_s.db, definition);

    Function::new(node_ref, Some(func_class))
}

pub(crate) enum UnionValue<T, I: Iterator<Item = T>> {
    Single(T),
    Multiple(I),
    Any,
}

fn infer_overloaded_class_method(
    i_s: &InferenceState,
    class: Class,
    attribute_class: Class,
    o: &OverloadDefinition,
) -> Option<Inferred> {
    let functions: Box<[_]> = o
        .iter_functions()
        .filter_map(|callable| {
            let c = infer_class_method(i_s, class, attribute_class, callable, None)?;
            Some(Arc::new(c))
        })
        .collect();
    Some(Inferred::from_type(match functions.len() {
        0 => return None,
        1 => Type::Callable(functions.into_vec().into_iter().next().unwrap()),
        _ => Type::FunctionOverload(FunctionOverload::new(functions)),
    }))
}

pub fn infer_class_method_on_instance<'db: 'class, 'class>(
    i_s: &InferenceState<'db, '_>,
    instance: &Type,
    func_class: Class,
    callable: &CallableContent,
) -> Option<CallableContent> {
    proper_classmethod_callable(
        i_s,
        callable,
        &func_class,
        None,
        || instance.clone(),
        || Type::Type(Arc::new(instance.clone())),
    )
}

pub fn infer_class_method<'db: 'class, 'class>(
    i_s: &InferenceState<'db, '_>,
    mut class: Class<'class>,
    func_class: Class,
    callable: &CallableContent,
    as_type_type: Option<&dyn Fn() -> Type>,
) -> Option<CallableContent> {
    let mut func_class = func_class;
    let class_generics_not_defined_yet = matches!(class.generics, Generics::NotDefinedYet { .. })
        && !class.type_vars(i_s).is_empty();
    if class_generics_not_defined_yet {
        // Check why this is necessary by following class_generics_not_defined_yet.
        let self_generics = Generics::Self_ {
            class_ref: class.node_ref,
        };
        class.generics = self_generics;
        if matches!(func_class.generics, Generics::NotDefinedYet { .. }) {
            func_class.generics = self_generics;
        }
    }

    proper_classmethod_callable(
        i_s,
        callable,
        &func_class,
        class_generics_not_defined_yet.then_some(class),
        || match as_type_type {
            Some(as_type_type) => match as_type_type() {
                Type::Type(t) => (*t).clone(),
                _ => unreachable!(),
            },
            None => class.as_type(i_s.db),
        },
        || match as_type_type {
            Some(as_type_type) => as_type_type(),
            None => class.as_type_type(i_s.db),
        },
    )
}

fn proper_classmethod_callable(
    i_s: &InferenceState,
    original_callable: &CallableContent,
    func_class: &Class,
    class_generics_not_defined_yet: Option<Class>,
    as_type: impl Fn() -> Type,
    as_type_type: impl Fn() -> Type,
) -> Option<CallableContent> {
    let mut class_method_type_var_usage = None;
    let mut callable = original_callable.clone();
    let mut type_vars = callable.type_vars.as_vec();
    match &callable.params {
        CallableParams::Simple(params) => {
            let mut vec = params.to_vec();
            // The first argument in a class param is not relevant if we execute descriptors.
            if vec.is_empty() {
                return None;
            }
            let first_param = vec.remove(0);

            if let Some(t) = first_param.type_.maybe_positional_type() {
                callable.params = CallableParams::Simple(Arc::from(vec));
                let c = Callable::new(original_callable, None);
                let mut matcher = Matcher::new_callable_matcher(&c);
                let t = replace_class_type_vars(i_s.db, t, func_class, &|| Some(as_type()));
                if !t
                    .is_super_type_of(i_s, &mut matcher, &as_type_type())
                    .bool()
                {
                    return None;
                }
                if let Type::Type(t) = t.as_ref()
                    && let Type::TypeVar(usage) = t.as_ref()
                {
                    class_method_type_var_usage = Some(usage.clone());
                    type_vars.remove(0);
                }
                if matcher.has_type_var_matcher() && class_method_type_var_usage.is_none() {
                    callable = callable.replace_type_var_likes_and_self_inplace(
                        i_s.db,
                        &mut |usage| matcher.replace_usage_if_calculated(i_s.db, usage),
                        &|| None,
                    )
                }
            }
        }
        CallableParams::Any(_) => (),
    };

    let type_vars = RefCell::new(type_vars);

    let callable_defined_at = callable.defined_at;
    let ensure_classmethod_type_var_like = |tvl| {
        let pos = type_vars.borrow().iter().position(|t| t == &tvl);
        let position = pos.unwrap_or_else(|| {
            type_vars.borrow_mut().push(tvl.clone());
            type_vars.borrow().len() - 1
        });
        tvl.as_type_var_like_usage(position.into(), callable_defined_at)
            .into_generic_item()
    };
    let get_class_method_class = || {
        if let Some(class) = class_generics_not_defined_yet {
            let type_var_likes = class.use_cached_type_vars(i_s.db);
            Type::new_class(
                class.node_ref.as_link(),
                match type_var_likes.is_empty() {
                    true => ClassGenerics::new_none(),
                    false => ClassGenerics::List(GenericsList::new_generics(
                        type_var_likes
                            .iter()
                            .map(|tvl| ensure_classmethod_type_var_like(tvl.clone()))
                            .collect(),
                    )),
                },
            )
        } else {
            as_type()
        }
    };
    let mut new_callable = callable.replace_type_var_likes_and_self_inplace(
        i_s.db,
        &mut |mut usage| {
            let in_definition = usage.in_definition();
            if let Some(result) = maybe_class_usage(i_s.db, func_class, &usage) {
                // We need to remap again, because in generics of classes will be
                // generic in the function of the classmethod, see for example
                // `testGenericClassMethodUnboundOnClass`.
                if let Some(class) = class_generics_not_defined_yet {
                    return result.replace_type_var_likes_and_self(
                        i_s.db,
                        &mut |usage| {
                            if usage.in_definition() == class.node_ref.as_link() {
                                let tvl = usage.as_type_var_like();
                                Some(ensure_classmethod_type_var_like(tvl))
                            } else {
                                None
                            }
                        },
                        &|| None,
                    );
                }
                Some(result)
            } else if in_definition == callable_defined_at {
                if let Some(u) = &class_method_type_var_usage {
                    return if u.index == usage.index() {
                        Some(GenericItem::TypeArg(get_class_method_class()))
                    } else {
                        usage.add_to_index(-1);
                        Some(usage.into_generic_item())
                    };
                }
                None
            } else {
                // This can happen for example if the return value is a Callable with its
                // own type vars.
                None
            }
        },
        &|| Some(get_class_method_class()),
    );
    let type_vars = type_vars.into_inner();
    new_callable.type_vars = TypeVarLikes::from_vec(type_vars);
    // We just skipped the first param, so from now on every param has an annotation, even if it's
    // an implicit Type::Any.
    new_callable
        .kind
        .update_had_first_self_or_class_annotation(true);
    Some(new_callable)
}

fn callable_into_inferred(callable: CallableContent) -> Inferred {
    Inferred::from_type(Type::Callable(Arc::new(callable)))
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
        _ => {
            unreachable!("Classes are handled earlier {complex:?}")
        }
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
        x => unreachable!("{x:?}"),
    }
}

pub fn specific_to_type<'db>(
    i_s: &InferenceState<'db, '_>,
    definition: NodeRef<'db>,
    specific: Specific,
) -> Cow<'db, Type> {
    match specific {
        Specific::AnyDueToError | Specific::InvalidTypeDefinition | Specific::PyTypedMissing => {
            Cow::Borrowed(&Type::ERROR)
        }
        Specific::ModuleNotFound => Cow::Borrowed(&Type::Any(AnyCause::ModuleNotFound)),
        Specific::Cycle => Cow::Borrowed(&Type::Any(AnyCause::Todo)),
        Specific::IntLiteral => Cow::Owned(Type::Literal(DbLiteral {
            kind: LiteralKind::Int(definition.expect_int().parse()),
            implicit: true,
        })),
        Specific::StringLiteral => Cow::Owned(Type::Literal(DbLiteral {
            kind: LiteralKind::String(
                DbString::from_python_string(
                    definition.file_index(),
                    definition.maybe_str().unwrap().as_python_string(),
                )
                .unwrap(),
            ),
            implicit: true,
        })),
        Specific::BoolLiteral => Cow::Owned(Type::Literal(DbLiteral {
            kind: LiteralKind::Bool(definition.as_code() == "True"),
            implicit: true,
        })),
        Specific::BytesLiteral => Cow::Owned(Type::Literal(DbLiteral {
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
        actual => unreachable!("{actual:?}"),
    }
}

fn infer_callable_with_first_param_annotation(
    i_s: &InferenceState,
    func: Function,
    first_type: &Type,
    attribute_class: &Class,
    instance: Type,
    add_issue: impl Fn(IssueKind),
) -> Inferred {
    let as_instance = || instance.clone();
    let mut matcher = Matcher::new_function_matcher(&func, func.type_vars(i_s.db), &as_instance);
    // If __call__ has a self type that is a Callable, just ignore it,
    // because that causes a recursion. It is how Mypy does it in
    // c68bd7ae2cffe8f0377ea9aab54b963b9fac3231
    if !(matches!(first_type, Type::Callable(_)) && func.name() == "__call__")
        && !match_self_type(i_s, &mut matcher, &instance, &attribute_class, first_type)
    {
        add_issue(IssueKind::InvalidSelfArgument {
            argument_type: instance.format_short(i_s.db),
            function_name: Box::from(func.name()),
            callable: func
                .as_type(i_s, FirstParamProperties::None)
                .format_short(i_s.db),
        });
    }
    let callable = func.as_callable(
        i_s,
        FirstParamProperties::Skip {
            to_self_instance: &|| instance.clone(),
        },
    );
    Inferred::new_unsaved_complex(ComplexPoint::TypeInstance(Type::Callable(Arc::new(
        matcher.remove_self_from_callable(i_s, callable),
    ))))
}

enum ApplyDescriptorsKind {
    All,
    NoBoundMethod,
}

#[derive(Copy, Clone)]
pub(crate) enum ApplyClassDescriptorsOrigin {
    ClassAccess,
    AssignToClass,
    InstanceSetattrAccess,
    AssignContext,
}

impl ApplyClassDescriptorsOrigin {
    pub fn should_apply(&self) -> bool {
        matches!(self, Self::ClassAccess)
    }

    fn should_add_ambigous_class_var_access(&self) -> bool {
        matches!(self, Self::ClassAccess | Self::AssignToClass)
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

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum AttributeKind {
    AnnotatedAttribute,
    Attribute,
    ClassVar,
    Final,
    Property {
        setter_type: Option<Arc<PropertySetter>>,
        is_final: bool,
        is_abstract: bool,
    },
    Classmethod {
        is_final: bool,
    },
    Staticmethod {
        is_final: bool,
    },
    DefMethod {
        is_final: bool,
    },
}

impl AttributeKind {
    pub fn is_read_only_property(&self) -> bool {
        matches!(
            self,
            Self::Property {
                setter_type: None,
                ..
            }
        )
    }

    pub fn classmethod_or_staticmethod(&self) -> bool {
        matches!(self, Self::Classmethod { .. } | Self::Staticmethod { .. })
    }

    pub fn classvar_like(&self) -> bool {
        matches!(
            self,
            Self::ClassVar
                | Self::DefMethod { .. }
                | Self::Property { .. }
                | Self::Classmethod { .. }
                | Self::Staticmethod { .. }
        )
    }

    pub fn is_final(&self) -> bool {
        matches!(
            self,
            Self::Final
                | Self::DefMethod { is_final: true, .. }
                | Self::Property { is_final: true, .. }
                | Self::Classmethod { is_final: true, .. }
                | Self::Staticmethod { is_final: true, .. }
        )
    }

    pub(crate) fn is_writable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn is_overwritable(&self) -> bool {
        matches!(
            self,
            Self::Attribute
                | Self::AnnotatedAttribute
                | Self::ClassVar
                | Self::Property {
                    is_abstract: false,
                    ..
                }
                | Self::Property {
                    is_abstract: true,
                    setter_type: Some(_),
                    ..
                }
        )
    }

    pub(crate) fn property_setter_type(&self) -> Option<&Type> {
        if let Self::Property { setter_type, .. } = self {
            match &setter_type.as_ref()?.type_ {
                PropertySetterType::OtherType(t) => Some(t),
                PropertySetterType::SameTypeFromCachedProperty => None,
            }
        } else {
            None
        }
    }

    pub fn is_cached_property(&self) -> bool {
        if let Self::Property { setter_type, .. } = self {
            matches!(
                setter_type.as_ref().map(|s| &s.type_),
                Some(PropertySetterType::SameTypeFromCachedProperty)
            )
        } else {
            false
        }
    }
}
