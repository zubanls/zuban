use std::{borrow::Cow, cell::RefCell, rc::Rc};

use parsa_python_cst::{
    NodeIndex, ParamKind, PrimaryContent, PythonString, SliceType as CSTSliceType,
};

use crate::{
    arguments::{Args, CombinedArgs, InferredArg, KnownArgs, KnownArgsWithCustomAddIssue},
    database::{
        ComplexPoint, Database, FileIndex, Locality, OverloadDefinition, Point, PointKind,
        PointLink, Specific,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        maybe_saved_annotation, on_argument_type_error, use_cached_annotation_or_type_comment,
        File, PythonFile,
    },
    format_data::FormatData,
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    matching::{
        calculate_property_return, create_signature_without_self_for_callable, match_self_type,
        maybe_class_usage, replace_class_type_vars, ErrorStrs, ErrorTypes, Generics, GotType,
        IteratorContent, LookupKind, Match, Matcher, OnLookupError, OnTypeError, ResultContext,
    },
    new_class,
    node_ref::NodeRef,
    type_::{
        execute_collections_named_tuple, execute_type_of_type, execute_typing_named_tuple,
        new_typed_dict, AnyCause, CallableContent, CallableLike, CallableParams, ClassGenerics,
        DbString, FunctionKind, FunctionOverload, GenericClass, GenericItem, GenericsList,
        IterInfos, Literal as DbLiteral, LiteralKind, LiteralValue, LookupResult, NeverCause, Type,
        TypeVarKind, TypeVarLike, TypeVarLikes,
    },
    type_helpers::{
        execute_assert_type, execute_cast, execute_isinstance, execute_issubclass,
        execute_new_type, execute_param_spec_class, execute_reveal_type, execute_super,
        execute_type, execute_type_var_class, execute_type_var_tuple_class, BoundMethod,
        BoundMethodFunction, Class, FirstParamProperties, Function, Instance, LookupDetails,
        OverloadedFunction, TypeOrClass,
    },
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub struct MroIndex(pub u32);

impl From<usize> for MroIndex {
    fn from(item: usize) -> Self {
        Self(item as u32)
    }
}

#[derive(Debug)]
pub enum FunctionOrOverload<'a> {
    Function(Function<'a, 'a>),
    Callable(Rc<CallableContent>),
    Overload(OverloadedFunction<'a>),
}

#[derive(Debug, Clone, PartialEq)]
enum InferredState {
    Saved(PointLink),
    UnsavedFileReference(FileIndex),
    UnsavedComplex(ComplexPoint),
    UnsavedSpecific(Specific),
    BoundMethod {
        instance: Type,
        mro_index: MroIndex,
        func_link: PointLink,
    },
}

#[derive(Clone, Debug)]
pub struct Inferred {
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
            state: InferredState::Saved(PointLink::new(file.file_index(), node_index)),
        }
    }

    pub fn new_unsaved_complex(complex: ComplexPoint) -> Self {
        Self {
            state: InferredState::UnsavedComplex(complex),
        }
    }

    fn new_bound_method(instance: Type, mro_index: MroIndex, func_link: PointLink) -> Self {
        Self {
            state: InferredState::BoundMethod {
                instance,
                mro_index,
                func_link,
            },
        }
    }

    pub fn new_cycle() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::Cycle),
        }
    }

    pub fn new_none() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::None),
        }
    }

    pub fn new_invalid_type_definition() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::InvalidTypeDefinition),
        }
    }

    pub fn new_module_not_found() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::ModuleNotFound),
        }
    }

    pub fn new_object(db: &Database) -> Self {
        Self::from_type(db.python_state.object_type())
    }

    pub fn new_list_of(db: &Database, inner: Type) -> Self {
        Self::from_type(new_class!(db.python_state.list_node_ref().as_link(), inner,))
    }

    pub fn new_any_from_error() -> Self {
        Self::from_type(Type::Any(AnyCause::FromError))
    }

    pub fn new_any(cause: AnyCause) -> Self {
        Self::from_type(Type::Any(cause))
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
                Specific::None => Cow::Borrowed(&Type::None),
                Specific::Cycle | Specific::ModuleNotFound => {
                    Cow::Borrowed(&Type::Any(AnyCause::Todo))
                }
                _ => unreachable!("{specific:?}"),
            },
            InferredState::UnsavedFileReference(file_index) => {
                Cow::Owned(Type::Module(*file_index))
            }
            InferredState::BoundMethod {
                instance,
                mro_index,
                func_link,
            } => {
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
        let instance_class = match instance {
            Type::Class(c) => c.class(i_s.db),
            Type::Type(t) => match t.as_ref() {
                Type::Class(c) => c
                    .class(i_s.db)
                    .use_cached_class_infos(i_s.db)
                    .metaclass(i_s.db),
                Type::TypeVar(tv) => match &tv.type_var.kind {
                    TypeVarKind::Bound(bound) => {
                        // TODO should this case be handled?
                        bound
                            .maybe_class(i_s.db)
                            .unwrap()
                            .use_cached_class_infos(i_s.db)
                            .metaclass(i_s.db)
                    }
                    _ => unreachable!(),
                },
                Type::Self_ => i_s
                    .current_class()
                    .unwrap()
                    .use_cached_class_infos(i_s.db)
                    .metaclass(i_s.db),
                _ => unreachable!(),
            },
            Type::Self_ => *i_s.current_class().unwrap(),
            Type::TypedDict(_) => i_s.db.python_state.typed_dict_class(),
            Type::Enum(enum_) => enum_.class(i_s.db),
            Type::TypeVar(tv) => match &tv.type_var.kind {
                TypeVarKind::Bound(t) => Self::load_bound_method_class(i_s, t, mro_index),
                _ => unreachable!(),
            },
            Type::Dataclass(d) => d.class(i_s.db),
            _ => unreachable!(),
        };
        let class_t = instance_class
            .mro(i_s.db)
            .nth(mro_index.0 as usize)
            .unwrap()
            .1;
        // Mro classes are never owned, because they are saved on classes.
        match class_t {
            TypeOrClass::Class(class) => class,
            TypeOrClass::Type(t) => match t {
                Cow::Borrowed(Type::Dataclass(d)) => d.class(i_s.db),
                Cow::Borrowed(Type::TypedDict(d)) => todo!("is this even necessary?"),
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

    pub fn maybe_new_partial(&self, i_s: &InferenceState, from: NodeRef) -> Option<Inferred> {
        if self.maybe_saved_specific(i_s.db) == Some(Specific::None) {
            return Some(Self {
                state: InferredState::UnsavedSpecific(Specific::PartialNone),
            });
        }
        let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(i_s.db) else {
            return None;
        };
        let check_for_partial = || {
            let Type::Class(GenericClass {
                link,
                generics: ClassGenerics::List(generics),
            }) = t
            else {
                return None;
            };
            let specific = if *link == i_s.db.python_state.list_node_ref().as_link() {
                Specific::PartialList
            } else if *link == i_s.db.python_state.dict_node_ref().as_link() {
                Specific::PartialDict
            } else if *link == i_s.db.python_state.set_node_ref().as_link() {
                Specific::PartialSet
            } else {
                return None;
            };
            for generic in generics.iter() {
                if !matches!(
                    generic,
                    GenericItem::TypeArg(Type::Never(NeverCause::Inference))
                ) {
                    return None;
                }
            }
            Some(Self {
                state: InferredState::UnsavedSpecific(specific),
            })
        };
        check_for_partial().or_else(|| {
            if t.has_never_from_inference(i_s.db) {
                from.add_issue(
                    i_s,
                    IssueKind::NeedTypeAnnotation {
                        for_: from.as_code().into(),
                        hint: None,
                    },
                )
            }
            None
        })
    }

    pub fn resolve_untyped_function_return(self, i_s: &InferenceState) -> Self {
        todo!();
        /*
        if let InferredState::Saved(definition) = self.state {
            let definition = NodeRef::from_link(i_s.db, definition);
            let point = definition.point();
            if point.type_() == PointType::Specific && point.specific() == Specific::Closure {
                todo!()
            }
        }
        self.resolve_class_type_vars(i_s, class, attribute_class)
        */
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
                    Specific::Param | Specific::MaybeSelfParam => {
                        todo!("might not even happen - remove")
                        //return i_s.infer_param(&definition);
                    }
                    Specific::AnnotationOrTypeCommentWithTypeVars
                    | Specific::AnnotationOrTypeCommentFinal => {
                        let t = use_cached_annotation_or_type_comment(i_s, definition);
                        if attribute_class.needs_generic_remapping_for_attributes(i_s, &t) {
                            let d = replace_class_type_vars(i_s.db, &t, attribute_class, &|| {
                                class.as_type(i_s.db)
                            });
                            return Inferred::from_type(d);
                        }
                    }
                    _ => (),
                }
            }
        }
        self
    }

    pub fn expect_class_or_simple_generic(&self, i_s: &InferenceState<'db, '_>) -> Cow<'db, Type> {
        let mut generics = ClassGenerics::None;
        if let InferredState::Saved(link) = &self.state {
            let definition = NodeRef::from_link(i_s.db, *link);
            let point = definition.point();
            if point.kind() == PointKind::Specific {
                generics = Self::expect_class_generics(definition, point);
            }
        }
        let link = self.get_class_link(i_s);
        Cow::Owned(Type::new_class(link, generics))
    }

    fn get_class_link(&self, i_s: &InferenceState) -> PointLink {
        let InferredState::Saved(link) = &self.state else {
            unreachable!()
        };
        let node_ref = NodeRef::from_link(i_s.db, *link);
        let point = node_ref.point();
        match point.kind() {
            PointKind::Complex => {
                let complex = node_ref.file.complex_points.get(point.complex_index());
                let ComplexPoint::Class(c) = complex else {
                    unreachable!();
                };
                node_ref.ensure_cached_class_infos(i_s);
                *link
            }
            PointKind::Specific => match point.specific() {
                Specific::SimpleGeneric => {
                    let inferred = node_ref
                        .file
                        .inference(i_s)
                        .infer_primary_or_atom(node_ref.as_primary().first());
                    inferred.get_class_link(i_s)
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    pub fn maybe_complex_point(&'slf self, db: &'db Database) -> Option<&'slf ComplexPoint> {
        match &self.state {
            InferredState::Saved(definition) => NodeRef::from_link(db, *definition).complex(),
            InferredState::UnsavedComplex(t) => Some(t),
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
                        kind: LiteralKind::Int(node_ref.expect_int().parse().unwrap()),
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
        if let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(db) {
            from_type(t)
        } else {
            UnionValue::Any
        }
    }

    pub fn run_on_int_literals(
        &self,
        i_s: &InferenceState,
        callable: impl Fn(isize) -> Option<Inferred>,
    ) -> Option<Inferred> {
        let infer = |i_s: &InferenceState, literal: DbLiteral| {
            if !matches!(literal.kind, LiteralKind::Int(_)) {
                return None;
            }
            let LiteralValue::Int(i) = literal.value(i_s.db) else {
                unreachable!();
            };
            let index = isize::try_from(i).ok().unwrap_or_else(|| todo!());
            callable(index)
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

    pub fn maybe_str(&self, db: &'db Database) -> Option<PythonString<'db>> {
        if let InferredState::Saved(link) = self.state {
            let node_ref = NodeRef::from_link(db, link);
            if let Some(Specific::String) = node_ref.point().maybe_specific() {
                return node_ref.infer_str();
            }
        }
        None
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
                    && !matches!(p.maybe_specific(), Some(Specific::String | Specific::Cycle))
                {
                    if ignore_if_already_saved {
                        return self;
                    }
                    let node_ref = NodeRef::new(file, index);
                    todo!(
                        "{self:?} >>>> {p:?} {index:?}, {}, {:?}",
                        file.tree.short_debug_of_index(index),
                        node_ref.complex()
                    );
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
            InferredState::BoundMethod {
                instance,
                mro_index,
                func_link,
            } => {
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

    pub fn init_as_function<'a>(
        &self,
        i_s: &InferenceState<'db, '_>,
        class: Option<Class<'a>>,
    ) -> Option<FunctionOrOverload<'a>>
    where
        'db: 'a,
    {
        match &self.state {
            InferredState::Saved(link) => {
                let definition = NodeRef::from_link(i_s.db, *link);
                match definition.point().maybe_specific() {
                    Some(Specific::Function) => {
                        return Some(FunctionOrOverload::Function(Function::new(
                            definition, class,
                        )));
                    }
                    _ => (),
                }
                match definition.complex() {
                    Some(ComplexPoint::FunctionOverload(overload)) => {
                        return Some(FunctionOrOverload::Overload(OverloadedFunction::new(
                            &overload.functions,
                            class,
                        )));
                    }
                    Some(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                        return Some(FunctionOrOverload::Callable(c.clone()));
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                return Some(FunctionOrOverload::Callable(c.clone()));
            }
            _ => (),
        }
        None
    }

    pub fn avoid_implicit_literal(self, i_s: &InferenceState) -> Self {
        if i_s.is_calculating_enum_members() {
            return self;
        }
        match self.state {
            InferredState::Saved(link) => {
                let node_ref = NodeRef::from_link(i_s.db, link);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => {
                        if !matches!(
                            point.specific(),
                            Specific::IntLiteral
                                | Specific::StringLiteral
                                | Specific::BytesLiteral
                                | Specific::BoolLiteral
                                | Specific::AnnotationOrTypeCommentFinal
                        ) {
                            return self;
                        }
                    }
                    PointKind::Complex => {
                        if !matches!(node_ref.complex().unwrap(), ComplexPoint::TypeInstance(_)) {
                            return self;
                        }
                    }
                    _ => return self,
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(_)) => (),
            _ => return self,
        }
        if let Some(t) = self.as_cow_type(i_s).maybe_avoid_implicit_literal(i_s.db) {
            Self::from_type(t)
        } else {
            self
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
        result.unwrap_or_else(|| Inferred::from_type(Type::Never(NeverCause::Other)))
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
        result.unwrap_or_else(|| Inferred::from_type(Type::Never(NeverCause::Other)))
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
                                let as_instance = || instance.clone();
                                let mut matcher = Matcher::new_function_matcher(
                                    func,
                                    func.type_vars(i_s),
                                    &as_instance,
                                );
                                // If __call__ has a self type that is a Callable, just ignore it,
                                // because that causes a recursion. It is how Mypy does it in
                                // c68bd7ae2cffe8f0377ea9aab54b963b9fac3231.
                                if !(matches!(first_type.as_ref(), Type::Callable(_))
                                    && func.name() == "__call__")
                                    && !match_self_type(
                                        i_s,
                                        &mut matcher,
                                        &instance,
                                        &attribute_class,
                                        &first_type,
                                    )
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
                                Some((
                                    Self::new_unsaved_complex(ComplexPoint::TypeInstance(
                                        Type::Callable(Rc::new(
                                            matcher.remove_self_from_callable(i_s, callable),
                                        )),
                                    )),
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
                        specific @ (Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentFinal) => {
                            let mut t = use_cached_annotation_or_type_comment(i_s, node_ref);
                            let is_remapped = matches!(
                                specific,
                                Specific::AnnotationOrTypeCommentWithTypeVars
                                | Specific::AnnotationOrTypeCommentFinal
                                if !attribute_class.needs_generic_remapping_for_attributes(i_s, &t)
                            );
                            if is_remapped {
                                t = Cow::Owned(replace_class_type_vars(
                                    i_s.db,
                                    &t,
                                    &attribute_class,
                                    &|| instance.clone(),
                                ));
                            }
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
                                mro_index,
                                &t,
                                if is_class_var {
                                    ApplyDescriptorsKind::All
                                } else {
                                    ApplyDescriptorsKind::NoBoundMethod
                                },
                            ) {
                                return r.map(|(inf, _)| (inf, attr_kind));
                            }
                            if is_remapped {
                                return Some((Inferred::from_type(t.into_owned()), attr_kind));
                            }
                            return Some((self, attr_kind));
                        }
                        _ => (),
                    },
                    PointKind::Complex => {
                        match node_ref.complex().unwrap() {
                            ComplexPoint::FunctionOverload(o) => {
                                let kind = o.kind();
                                let attr_kind = match kind {
                                    FunctionKind::Staticmethod => {
                                        return Some((
                                            self,
                                            AttributeKind::Staticmethod {
                                                is_final: o.is_final,
                                            },
                                        ))
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
                                            .map(Rc::new)
                                        })
                                        .collect();
                                    match results.len() {
                                        0 => {
                                            let overload = OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            );
                                            let t = IssueKind::InvalidClassMethodFirstArgument {
                                                argument_type: Type::Type(Rc::new(instance))
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
                                    mro_index,
                                    t,
                                    apply_descriptors_kind,
                                ) {
                                    return inf;
                                }
                            }
                            ComplexPoint::Class(cls_storage) => {
                                let class = Class::new(
                                    node_ref,
                                    cls_storage,
                                    Generics::NotDefinedYet,
                                    None,
                                );
                                debug!("TODO class descriptors");
                            }
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex {
                    if let Some(inf) = Self::bind_instance_descriptors_for_type(
                        i_s,
                        for_name,
                        instance,
                        attribute_class,
                        add_issue,
                        mro_index,
                        t,
                        apply_descriptors_kind,
                    ) {
                        return inf;
                    }
                }
            }
            InferredState::UnsavedSpecific(specific) => {
                todo!("{specific:?} {}", instance.format_short(i_s.db))
            }
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::BoundMethod { .. } => todo!(),
        }
        Some((self, AttributeKind::Attribute))
    }

    fn bind_instance_descriptors_for_type(
        i_s: &InferenceState,
        for_name: &str,
        instance: Type,
        attribute_class: Class,
        add_issue: impl Fn(IssueKind),
        mro_index: MroIndex,
        t: &Type,
        apply_descriptors_kind: ApplyDescriptorsKind,
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
            Type::Callable(c) => match c.kind {
                FunctionKind::Function { .. }
                    if !matches!(apply_descriptors_kind, ApplyDescriptorsKind::NoBoundMethod) =>
                {
                    debug_assert!(matches!(c.kind, FunctionKind::Function { .. }));
                    if let Some(f) = c.first_positional_type() {
                        let new_c = create_signature_without_self_for_callable(
                            i_s,
                            c,
                            &instance,
                            &attribute_class,
                            &f,
                        )
                        .map(Rc::new)
                        .unwrap_or_else(|| {
                            add_invalid_self_arg(c);
                            i_s.db.python_state.any_callable_from_error.clone()
                        });
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
                FunctionKind::Property { writable, .. } => {
                    let first = c.first_positional_type();
                    return Some(Some(
                        if let Some(t) =
                            calculate_property_return(i_s, &instance, &attribute_class, c)
                        {
                            (
                                Inferred::from_type(t),
                                AttributeKind::Property {
                                    writable,
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
                    let result = infer_class_method_on_instance(i_s, &instance, attribute_class, c);
                    if result.is_none() {
                        let t = IssueKind::InvalidClassMethodFirstArgument {
                            argument_type: Type::Type(Rc::new(instance)).format_short(i_s.db),
                            function_name: c.name(i_s.db).into(),
                            callable: t.format_short(i_s.db),
                        };
                        add_issue(t);
                        return Some(Some((Self::new_any_from_error(), AttributeKind::Attribute)));
                    }
                    let is_final = c.is_final;
                    return Some(result.map(|c| {
                        (
                            callable_into_inferred(c),
                            AttributeKind::Classmethod { is_final },
                        )
                    }));
                }
                FunctionKind::Staticmethod => {
                    return Some(Some((
                        Inferred::from_type(t.clone()),
                        AttributeKind::Staticmethod {
                            is_final: c.is_final,
                        },
                    )))
                }
            },
            Type::CustomBehavior(custom) => {
                return Some(Some((
                    Inferred::from_type(Type::CustomBehavior(custom.bind(Rc::new(instance)))),
                    AttributeKind::DefMethod { is_final: false },
                )))
            }
            _ => (),
        }

        let mut new = None;
        if attribute_class.needs_generic_remapping_for_attributes(i_s, t) {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| instance.clone(),
            ));
            t = new.as_ref().unwrap();
        }

        if let Type::Class(c) = t {
            let potential_descriptor = use_instance_with_ref(
                NodeRef::from_link(i_s.db, c.link),
                Generics::from_class_generics(i_s.db, &c.generics),
                None,
            );
            if let Some(inf) = potential_descriptor.bind_dunder_get(i_s, add_issue, instance) {
                return Some(Some((inf, AttributeKind::Attribute)));
            }
        }
        if let Some(new) = new {
            return Some(Some((Inferred::from_type(new), AttributeKind::Attribute)));
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
        apply_descriptor: bool,
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
                            let t = func.as_type(
                                i_s,
                                FirstParamProperties::MethodAccessedOnClass { func_class_type },
                            );
                            return Some((
                                Inferred::from_type(t),
                                AttributeKind::DefMethod { is_final: false },
                            ));
                        }
                        specific @ (Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentFinal) => {
                            if specific == Specific::AnnotationOrTypeCommentWithTypeVars
                                && apply_descriptor
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
                                apply_descriptor,
                                &t,
                                as_type_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        _ => (),
                    },
                    PointKind::Complex => match node_ref.complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => match o.kind() {
                            FunctionKind::Function { .. } => {
                                return Some((
                                    Inferred::from_type(Type::FunctionOverload(
                                        FunctionOverload::new(
                                            o.iter_functions()
                                                .map(|c| {
                                                    c.merge_class_type_vars(
                                                        i_s.db,
                                                        *class,
                                                        attribute_class,
                                                    )
                                                })
                                                .collect(),
                                        ),
                                    )),
                                    AttributeKind::Attribute,
                                ))
                            }
                            FunctionKind::Property { .. } => unreachable!(),
                            FunctionKind::Classmethod { .. } => {
                                let Some(inf) =
                                    infer_overloaded_class_method(i_s, *class, attribute_class, o)
                                else {
                                    add_issue(IssueKind::InvalidSelfArgument {
                                        argument_type: class.as_type_type(i_s).format_short(i_s.db),
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
                                apply_descriptor,
                                t,
                                as_type_type,
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
                                apply_descriptor,
                                t,
                                as_type_type,
                            ) {
                                return r.map(|inf| (inf, attr_kind));
                            }
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => {
                if let ComplexPoint::TypeInstance(t) = complex {
                    if let Some(inf) = Self::bind_class_descriptors_for_type(
                        i_s,
                        class,
                        attribute_class,
                        add_issue,
                        apply_descriptor,
                        t,
                        as_type_type,
                    ) {
                        return inf.map(|inf| (inf, AttributeKind::Attribute));
                    }
                }
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::BoundMethod { .. } => todo!(),
        }
        Some((self, attr_kind))
    }

    pub(crate) fn bind_class_descriptors_for_type(
        i_s: &InferenceState,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        add_issue: impl Fn(IssueKind),
        apply_descriptor: bool,
        t: &Type,
        as_type_type: Option<&dyn Fn() -> Type>,
    ) -> Option<Option<Self>> {
        let mut t = t;
        if let Type::Callable(c) = t {
            match c.kind {
                FunctionKind::Function { .. } => (),
                FunctionKind::Property { .. } => {
                    return if apply_descriptor {
                        Some(Some(Inferred::from_type(
                            i_s.db.python_state.property_type(),
                        )))
                    } else {
                        None
                    }
                }
                FunctionKind::Classmethod { .. } => {
                    let result = infer_class_method(i_s, *class, attribute_class, c, as_type_type);
                    if result.is_none() {
                        let inv = IssueKind::InvalidSelfArgument {
                            argument_type: class.as_type_type(i_s).format_short(i_s.db),
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
                    if let Some(as_type_type) = as_type_type {
                        let Type::Type(t) = as_type_type() else {
                            unreachable!()
                        };
                        (*t).clone()
                    } else {
                        class.as_type(i_s.db)
                    }
                },
            ));
            t = new.as_ref().unwrap();
        }

        if let Type::Class(c) = t {
            if apply_descriptor {
                let inst = use_instance_with_ref(
                    NodeRef::from_link(i_s.db, c.link),
                    Generics::from_class_generics(i_s.db, &c.generics),
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
        }
        if let Some(new) = new {
            return Some(Some(Inferred::from_type(new)));
        }
        None
    }

    pub fn bind_new_descriptors(
        self,
        i_s: &InferenceState,
        class: &Class,
        class_of_attribute: Option<Class>,
    ) -> Self {
        // This method exists for __new__
        let attribute_class = class_of_attribute.unwrap_or(*class);
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.kind() {
                    PointKind::Specific => match point.specific() {
                        Specific::Function => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            let result = infer_class_method(
                                i_s,
                                *class,
                                attribute_class,
                                &func.as_callable(i_s, FirstParamProperties::None),
                                None,
                            );
                            if let Some(result) = result {
                                return callable_into_inferred(result);
                            } else {
                                todo!()
                            }
                        }
                        _ => (),
                    },
                    PointKind::Complex => match node_ref.complex().unwrap() {
                        ComplexPoint::FunctionOverload(o) => {
                            let Some(inf) =
                                infer_overloaded_class_method(i_s, *class, attribute_class, o)
                            else {
                                todo!()
                            };
                            return inf;
                        }
                        ComplexPoint::TypeInstance(t @ Type::Callable(c)) => {
                            let Some(c) = infer_class_method(i_s, *class, attribute_class, c, None)
                            else {
                                todo!();
                            };
                            return Inferred::from_type(Type::Callable(Rc::new(c)));
                        }
                        _ => (),
                    },
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(Type::Callable(c))) => {
                // This is reached by NamedTuples. Not sure it this reached otherwise as well.
                let result = infer_class_method(i_s, *class, attribute_class, c, None);
                if let Some(result) = result {
                    return callable_into_inferred(result);
                } else {
                    todo!()
                }
            }
            InferredState::UnsavedComplex(complex) => (),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::BoundMethod { .. } => todo!(),
        }
        self
    }

    pub fn debug_info(&self, i_s: &InferenceState) -> String {
        let details = match &self.state {
            InferredState::Saved(definition) => {
                let definition = NodeRef::from_link(i_s.db, *definition);
                format!(
                    "{} (complex?: {:?})",
                    definition.debug_info(i_s.db),
                    definition.complex(),
                )
            }
            _ => "".to_owned(),
        };
        format!(
            "description = {}\ndebug = {self:?}\ndetails = {details}",
            "",
        )
    }

    fn expect_class_generics(definition: NodeRef, point: Point) -> ClassGenerics {
        debug_assert_eq!(point.kind(), PointKind::Specific);
        debug_assert_eq!(point.specific(), Specific::SimpleGeneric);
        let PrimaryContent::GetItem(slice_type) = definition.as_primary().second() else {
            unreachable!();
        };
        match slice_type {
            CSTSliceType::NamedExpression(named) => ClassGenerics::ExpressionWithClassType(
                PointLink::new(definition.file_index(), named.expression().index()),
            ),
            CSTSliceType::Slice(_) | CSTSliceType::StarredExpression(_) => unreachable!(),
            CSTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(PointLink::new(
                definition.file_index(),
                slices.index(),
            )),
        }
    }

    pub fn is_union_like(&self, i_s: &InferenceState) -> bool {
        self.as_cow_type(i_s).is_union_like(i_s.db)
    }

    #[inline]
    pub fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        in_file: &PythonFile,
        name: &str,
        kind: LookupKind,
        callable: &mut impl FnMut(&Type, LookupDetails),
    ) {
        self.as_cow_type(i_s).run_after_lookup_on_each_union_member(
            i_s,
            Some(self),
            in_file.file_index(),
            name,
            kind,
            &mut ResultContext::Unknown,
            &|issue| todo!(),
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
        self.lookup_with_result_context(i_s, node_ref, name, kind, &mut ResultContext::Unknown)
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
            from.file_index(),
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
        on_lookup_error: OnLookupError,
    ) -> Self {
        self.type_lookup_and_execute_with_details(
            i_s,
            in_file,
            name,
            args,
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
    ) -> Self {
        self.type_lookup_and_execute(i_s, from.file, name, args, &|t| {
            add_attribute_error(i_s, from, &self.as_cow_type(i_s), t, name)
        })
    }

    pub(crate) fn type_lookup_and_execute_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        in_file: &PythonFile,
        name: &str,
        args: &dyn Args<'db>,
        on_lookup_error: OnLookupError,
        on_type_error: OnTypeError,
    ) -> Self {
        let mut result: Option<Inferred> = None;
        self.run_after_lookup_on_each_union_member(
            i_s,
            in_file,
            name,
            LookupKind::OnlyType,
            &mut |_, lookup_result| {
                if matches!(lookup_result.lookup, LookupResult::None) {
                    on_lookup_error(&self.as_cow_type(i_s));
                }
                let inf = lookup_result.lookup.into_inferred().execute_with_details(
                    i_s,
                    args,
                    &mut ResultContext::ExpectUnused,
                    on_type_error,
                );
                result = if let Some(r) = result.take() {
                    Some(r.simplified_union(i_s, inf))
                } else {
                    Some(inf)
                }
            },
        );
        result.unwrap_or_else(|| todo!())
    }

    pub(crate) fn execute(&self, i_s: &InferenceState<'db, '_>, args: &dyn Args<'db>) -> Self {
        self.execute_with_details(
            i_s,
            args,
            &mut ResultContext::Unknown,
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
                        let specific = point.specific();
                        match specific {
                            Specific::Function => {
                                return Function::new(node_ref, None).execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::BuiltinsSuper => return execute_super(i_s, args),
                            Specific::BuiltinsIsinstance => return execute_isinstance(i_s, args),
                            Specific::BuiltinsIssubclass => return execute_issubclass(i_s, args),
                            Specific::TypingTypeVarClass => {
                                return execute_type_var_class(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingTypeVarTupleClass => {
                                return execute_type_var_tuple_class(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingParamSpecClass => {
                                return execute_param_spec_class(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingNamedTuple => {
                                return execute_typing_named_tuple(i_s, args)
                            }
                            Specific::TypingTypedDict => return new_typed_dict(i_s, args),
                            Specific::CollectionsNamedTuple => {
                                return execute_collections_named_tuple(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingType => return execute_type(i_s, args, on_type_error),
                            Specific::TypingTuple => {
                                return i_s
                                    .db
                                    .python_state
                                    .tuple_class_with_generics_to_be_defined()
                                    .execute(i_s, args, result_context, on_type_error, true)
                            }
                            Specific::TypingCast => {
                                return execute_cast(i_s, args, result_context, on_type_error)
                            }
                            Specific::RevealTypeFunction => {
                                return execute_reveal_type(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::AssertTypeFunction => {
                                return execute_assert_type(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingNewType => {
                                return execute_new_type(i_s, args, result_context, on_type_error)
                            }
                            Specific::TypingAny => {
                                args.add_issue(i_s, IssueKind::AnyNotCallable);
                                args.iter().calculate_diagnostics(i_s);
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
                                    .execute_with_details(i_s, args, result_context, on_type_error)
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
                                let c = Class::new(node_ref, cls, Generics::NotDefinedYet, None);
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
                            ComplexPoint::TypeAlias(alias) => {
                                if !alias.type_vars.is_empty() {
                                    if let Some(file) = args.in_file() {
                                        if file.flags(i_s.db).disallow_any_generics {
                                            node_ref.add_issue(
                                                i_s,
                                                IssueKind::MissingTypeParameters {
                                                    name: alias
                                                        .name(i_s.db)
                                                        .unwrap_or("<Alias>")
                                                        .into(),
                                                },
                                            );
                                        }
                                    }
                                }
                                if alias.application_allowed() {
                                    return execute_type_of_type(
                                        i_s,
                                        args,
                                        result_context,
                                        on_type_error,
                                        &alias.as_type_and_set_type_vars_any(i_s.db),
                                    );
                                }
                                args.add_issue(
                                    i_s,
                                    IssueKind::NotCallable {
                                        type_: Box::from("\"<typing special form>\""),
                                    },
                                );
                                return Inferred::new_any_from_error();
                            }
                            ComplexPoint::NewTypeDefinition(new_type) => {
                                let mut iterator = args.iter();
                                if let Some(first_arg) = iterator.next() {
                                    let t = new_type.type_(i_s);
                                    let InferredArg::Inferred(inf) =
                                        first_arg.infer(i_s, &mut ResultContext::Known(t))
                                    else {
                                        todo!()
                                    };
                                    let other = inf.as_cow_type(i_s);
                                    if let Match::False { ref reason, .. } =
                                        t.is_simple_super_type_of(i_s, &other)
                                    {
                                        (on_type_error.callback)(
                                            i_s,
                                            &|_| {
                                                Some(
                                                    format!(" to \"{}\"", new_type.name(i_s.db))
                                                        .into(),
                                                )
                                            },
                                            &first_arg,
                                            ErrorTypes {
                                                matcher: None,
                                                reason,
                                                got: GotType::Type(&other),
                                                expected: t,
                                            },
                                        );
                                    }
                                } else {
                                    args.add_issue(
                                        i_s,
                                        IssueKind::TooFewArguments(
                                            format!(" for \"{}\"", new_type.name(i_s.db)).into(),
                                        ),
                                    );
                                }
                                if iterator.next().is_some() {
                                    args.add_issue(
                                        i_s,
                                        IssueKind::TooManyArguments(
                                            format!(" for \"{}\"", new_type.name(i_s.db)).into(),
                                        ),
                                    );
                                }
                                return Self::from_type(Type::NewType(new_type.clone()));
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
            InferredState::BoundMethod {
                instance,
                mro_index,
                func_link,
            } => {
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
                    | Specific::TypingType
                    | Specific::TypingLiteral
                    | Specific::TypingAnnotated
                    | Specific::TypingNamedTuple
                    | Specific::CollectionsNamedTuple
                    | Specific::TypingCallable),
                ) => {
                    let result = slice_type
                        .file
                        .inference(i_s)
                        .compute_type_application_on_typing_class(
                            specific,
                            *slice_type,
                            matches!(result_context, ResultContext::AssignmentNewDefinition),
                        );
                    if matches!(
                        specific,
                        Specific::TypingAnnotated
                            | Specific::TypingTuple
                            | Specific::TypingUnion
                            | Specific::TypingCallable
                            | Specific::TypingOptional
                    ) {
                        return result;
                    }
                    return Inferred::from_type(i_s.db.python_state.typing_special_form_type());
                }
                Some(Specific::TypingClassVar) => {
                    return match slice_type.unpack() {
                        SliceTypeContent::Simple(simple) => {
                            // TODO if it is a (), it's am empty tuple
                            simple.infer(i_s, &mut ResultContext::Unknown)
                        }
                        _ => {
                            todo!()
                        }
                    };
                }
                _ => {
                    let node_ref = NodeRef::from_link(i_s.db, link);
                    match node_ref.complex() {
                        Some(ComplexPoint::TypeAlias(ta)) => {
                            return slice_type
                                .file
                                .inference(i_s)
                                .compute_type_application_on_alias(
                                    ta,
                                    *slice_type,
                                    matches!(
                                        result_context,
                                        ResultContext::AssignmentNewDefinition
                                    ),
                                )
                        }
                        _ => (),
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
            &|_| {
                slice_type.as_node_ref().add_issue(
                    i_s,
                    IssueKind::UnsupportedSetItemTarget(self.format_short(i_s)),
                )
            },
            OnTypeError::new(&|i_s, function, arg, types| {
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

    pub fn maybe_bound_method_of_function(&self) -> Option<PointLink> {
        match &self.state {
            InferredState::BoundMethod { func_link, .. } => Some(*func_link),
            _ => None,
        }
    }

    pub fn iter(self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
        self.as_cow_type(i_s).iter(
            i_s,
            IterInfos::new(from, &|issue| from.add_issue(i_s, issue)),
        )
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
}

fn load_bound_method<'db: 'a, 'a, 'b>(
    i_s: &InferenceState<'db, '_>,
    instance: &'b Type,
    class: Class<'a>,
    func_link: PointLink,
) -> BoundMethod<'a, 'b> {
    let reference = NodeRef::from_link(i_s.db, func_link);
    match reference.complex() {
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
    class_reference: NodeRef<'a>,
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
    let func = Function::new(node_ref, Some(func_class));
    func
}

pub enum UnionValue<T, I: Iterator<Item = T>> {
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
            Some(Rc::new(c))
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
        || Type::Type(Rc::new(instance.clone())),
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
    let class_generics_not_defined_yet =
        matches!(class.generics, Generics::NotDefinedYet) && !class.type_vars(i_s).is_empty();
    if class_generics_not_defined_yet {
        // Check why this is necessary by following class_generics_not_defined_yet.
        let self_generics = Generics::Self_ {
            type_var_likes: class.type_vars(i_s),
            class_definition: class.node_ref.as_link(),
        };
        class.generics = self_generics;
        func_class.generics = self_generics;
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
            None => class.as_type_type(i_s),
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
            let first_param = vec.remove(0);

            callable.params = CallableParams::Simple(Rc::from(vec));
            if let Some(t) = first_param.type_.maybe_positional_type() {
                let mut matcher = Matcher::new_callable_matcher(original_callable);
                let t = replace_class_type_vars(i_s.db, t, func_class, &as_type);
                if !t
                    .is_super_type_of(i_s, &mut matcher, &as_type_type())
                    .bool()
                {
                    return None;
                }
                if let Type::Type(t) = t {
                    if let Type::TypeVar(usage) = t.as_ref() {
                        class_method_type_var_usage = Some(usage.clone());
                        type_vars.remove(0);
                    }
                }
                if matcher.has_type_var_matcher() && class_method_type_var_usage.is_none() {
                    callable = callable.replace_type_var_likes_and_self(
                        i_s.db,
                        &mut |usage| matcher.replace_usage_if_calculated(i_s.db, usage),
                        &|| Type::Self_,
                    )
                }
            }
        }
        CallableParams::Any(_) | CallableParams::Never(_) => (),
    };

    let type_vars = RefCell::new(type_vars);

    let ensure_classmethod_type_var_like = |tvl| {
        let pos = type_vars.borrow().iter().position(|t| t == &tvl);
        let position = pos.unwrap_or_else(|| {
            type_vars.borrow_mut().push(tvl.clone());
            type_vars.borrow().len() - 1
        });
        tvl.as_type_var_like_usage(position.into(), callable.defined_at)
            .into_generic_item()
    };
    let get_class_method_class = || {
        if let Some(class) = class_generics_not_defined_yet {
            let type_var_likes = class.use_cached_type_vars(i_s.db);
            Type::new_class(
                class.node_ref.as_link(),
                match type_var_likes.len() {
                    0 => ClassGenerics::None,
                    _ => ClassGenerics::List(GenericsList::new_generics(
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
    let mut new_callable = callable.replace_type_var_likes_and_self(
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
                                ensure_classmethod_type_var_like(tvl)
                            } else {
                                usage.into_generic_item()
                            }
                        },
                        &|| todo!(),
                    );
                }
                result
            } else if in_definition == callable.defined_at {
                if let Some(u) = &class_method_type_var_usage {
                    if u.index == usage.index() {
                        return GenericItem::TypeArg(get_class_method_class());
                    } else {
                        usage.add_to_index(-1);
                        todo!()
                    }
                }
                usage.into_generic_item()
            } else {
                // This can happen for example if the return value is a Callable with its
                // own type vars.
                usage.into_generic_item()
            }
        },
        #[allow(clippy::redundant_closure)] // This is a clippy bug
        &|| get_class_method_class(),
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
    Inferred::from_type(Type::Callable(Rc::new(callable)))
}

fn type_of_complex<'db: 'x, 'x>(
    i_s: &InferenceState<'db, '_>,
    complex: &'x ComplexPoint,
    definition: Option<NodeRef<'x>>,
) -> Cow<'x, Type> {
    match complex {
        ComplexPoint::Class(cls_storage) => {
            definition.unwrap().ensure_cached_class_infos(i_s);
            let cls = Class::new(
                // This can only ever happen for saved definitions, therefore we can unwrap.
                definition.unwrap(),
                cls_storage,
                Generics::NotDefinedYet,
                None,
            );
            Cow::Owned(cls.as_type_type(i_s))
        }
        ComplexPoint::FunctionOverload(overload) => {
            let overload =
                OverloadedFunction::new(&overload.functions, i_s.current_class().copied());
            Cow::Owned(overload.as_type(i_s, None))
        }
        ComplexPoint::TypeInstance(t) => Cow::Borrowed(t),
        ComplexPoint::TypeAlias(alias) => Cow::Owned({
            if alias.type_if_valid().is_subclassable(i_s.db) {
                // TODO is this type correct with the Any?
                Type::Type(Rc::new(alias.as_type_and_set_type_vars_any(i_s.db)))
            } else {
                i_s.db.python_state.typing_special_form_type()
            }
        }),
        ComplexPoint::TypeVarLike(t) => match t {
            TypeVarLike::TypeVar(_) => Cow::Owned(i_s.db.python_state.type_var_type()),
            TypeVarLike::TypeVarTuple(_) => todo!(),
            TypeVarLike::ParamSpec(_) => todo!(),
        },
        ComplexPoint::NewTypeDefinition(n) => {
            Cow::Owned(Type::Type(Rc::new(Type::NewType(n.clone()))))
        }
        ComplexPoint::NamedTupleDefinition(n) => Cow::Owned(Type::Type(n.clone())),
        ComplexPoint::TypedDictDefinition(t) => Cow::Owned(Type::Type(t.type_.clone())),
        ComplexPoint::IndirectFinal(t) => Cow::Borrowed(t),
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
        Specific::AnyDueToError | Specific::InvalidTypeDefinition => {
            Cow::Borrowed(&Type::Any(AnyCause::FromError))
        }
        Specific::ModuleNotFound => Cow::Borrowed(&Type::Any(AnyCause::ModuleNotFound)),
        Specific::Cycle => Cow::Borrowed(&Type::Any(AnyCause::Todo)),
        Specific::IntLiteral => Cow::Owned(Type::Literal(DbLiteral {
            kind: LiteralKind::Int(definition.expect_int().parse().unwrap()),
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
            kind: LiteralKind::Bytes(definition.as_link()),
            implicit: true,
        })),
        Specific::String => Cow::Owned(i_s.db.python_state.str_type()),
        Specific::Int => Cow::Owned(i_s.db.python_state.int_type()),
        Specific::Float => Cow::Owned(i_s.db.python_state.float_type()),
        Specific::Bool => Cow::Owned(i_s.db.python_state.bool_type()),
        Specific::Bytes => Cow::Owned(i_s.db.python_state.bytes_type()),
        Specific::Complex => Cow::Owned(i_s.db.python_state.complex_type()),
        Specific::Ellipsis => Cow::Owned(i_s.db.python_state.ellipsis_type()),
        Specific::Function => Cow::Owned(
            Function::new(definition, i_s.current_class().copied())
                .as_type(i_s, FirstParamProperties::None),
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
            definition.add_need_type_annotation_issue(i_s, specific);
            Cow::Borrowed(&i_s.db.python_state.list_of_any)
        }
        Specific::PartialDict => {
            definition.add_need_type_annotation_issue(i_s, specific);
            Cow::Borrowed(&i_s.db.python_state.dict_of_any)
        }
        Specific::PartialSet => {
            definition.add_need_type_annotation_issue(i_s, specific);
            Cow::Borrowed(&i_s.db.python_state.set_of_any)
        }
        Specific::BuiltinsIsinstance => todo!(),
        Specific::BuiltinsIssubclass => todo!(),
        Specific::BuiltinsSuper => todo!(),
        Specific::TypingTypeVarClass => todo!(),
        Specific::TypingTypeVarTupleClass => todo!(),
        Specific::TypingParamSpecClass => todo!(),
        Specific::TypingType => Cow::Borrowed(&i_s.db.python_state.type_of_any),
        Specific::TypingTuple => Cow::Borrowed(&i_s.db.python_state.type_of_arbitrary_tuple),
        Specific::CollectionsNamedTuple => todo!(),
        Specific::TypingProtocol
        | Specific::TypingGeneric
        | Specific::TypingUnion
        | Specific::TypingOptional
        | Specific::TypingLiteral
        | Specific::TypingAnnotated
        | Specific::TypingNamedTuple
        | Specific::TypingTypedDict
        | Specific::TypingCallable => todo!(), //Cow::Owned(i_s.db.python_state.typing_special_form_type()),
        Specific::TypingCast => todo!(),
        Specific::TypingClassVar => todo!(),
        Specific::RevealTypeFunction => todo!(),
        Specific::None => Cow::Borrowed(&Type::None),
        Specific::TypingNewType => todo!(),
        // Typeshed defines this as object()
        Specific::TypingAny => Cow::Owned(i_s.db.python_state.object_type()),
        Specific::MypyExtensionsArg
        | Specific::MypyExtensionsDefaultArg
        | Specific::MypyExtensionsNamedArg
        | Specific::MypyExtensionsDefaultNamedArg
        | Specific::MypyExtensionsVarArg
        | Specific::MypyExtensionsKwArg => {
            i_s.db
                .python_state
                .mypy_extensions_arg_func(i_s.db, specific)
                .as_cow_type(i_s);
            todo!()
        }
        actual => unreachable!("{actual:?}"),
    }
}

enum ApplyDescriptorsKind {
    All,
    NoBoundMethod,
}

pub fn add_attribute_error(
    i_s: &InferenceState,
    node_ref: NodeRef,
    full_type: &Type,
    t: &Type,
    name: &str,
) {
    let object = match t {
        Type::Module(f) => {
            if !node_ref.file.flags(i_s.db).ignore_missing_imports {
                node_ref.add_issue(i_s, IssueKind::ModuleAttributeError { name: name.into() });
            }
            return;
        }
        _ => format!("\"{}\"", t.format_short(i_s.db)).into(),
    };
    let name = Box::from(name);
    if let Type::TypeVar(usage) = full_type {
        if let TypeVarKind::Bound(bound) = &usage.type_var.kind {
            if bound.is_union_like(i_s.db) {
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
        }
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

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum AttributeKind {
    AnnotatedAttribute,
    Attribute,
    ClassVar,
    Final,
    Property {
        writable: bool,
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
                writable: false,
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
                | Self::Property { writable: true, .. }
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
                    writable: true,
                    ..
                }
        )
    }
}
