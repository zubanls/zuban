use parsa_python_ast::{NodeIndex, PrimaryContent, PythonString, SliceType as ASTSliceType};
use std::cell::RefCell;
use std::rc::Rc;

use crate::arguments::{Arguments, CombinedArguments, KnownArguments};
use crate::database::{
    CallableContent, CallableParams, ClassGenerics, ComplexPoint, Database, DbString, DbType, Enum,
    FileIndex, FunctionKind, FunctionOverload, GenericClass, GenericItem, GenericsList,
    Literal as DbLiteral, LiteralKind, Locality, MroIndex, NewType, OverloadDefinition, Point,
    PointLink, PointType, Specific, TypeVarKind, TypeVarLike, TypeVarLikes,
};
use crate::debug;
use crate::diagnostics::IssueType;
use crate::file::{
    on_argument_type_error, use_cached_annotation_or_type_comment, File, PythonFile,
};
use crate::getitem::{SliceType, SliceTypeContent};
use crate::inference_state::InferenceState;
use crate::matching::{
    calculate_property_return, create_signature_without_self,
    create_signature_without_self_for_callable, maybe_class_usage, replace_class_type_vars,
    FormatData, Generics, IteratorContent, LookupKind, LookupResult, Matcher, OnLookupError,
    OnTypeError, ResultContext, Type,
};
use crate::node_ref::NodeRef;
use crate::type_helpers::{
    execute_assert_type, execute_collections_named_tuple, execute_super, execute_type,
    execute_typing_named_tuple, merge_class_type_vars_into_callable, new_typed_dict, BoundMethod,
    BoundMethodFunction, Class, FirstParamProperties, Function, Instance, NewTypeClass,
    OverloadedFunction, ParamSpecClass, RevealTypeFunction, TypeOrClass, TypeVarClass,
    TypeVarTupleClass, TypedDictHelper, TypingCast,
};

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
        instance: DbType,
        mro_index: MroIndex,
        func_link: PointLink,
    },
    Unknown,
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

    fn new_bound_method(instance: DbType, mro_index: MroIndex, func_link: PointLink) -> Self {
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

    pub fn new_unknown() -> Self {
        Self {
            state: InferredState::Unknown,
        }
    }

    pub fn new_none() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::None),
        }
    }

    pub fn new_any() -> Self {
        Self {
            state: InferredState::UnsavedSpecific(Specific::Any),
        }
    }

    pub fn new_file_reference(index: FileIndex) -> Self {
        // TODO maybe remove this and UnsavedFileReference??? unused??
        Self {
            state: InferredState::UnsavedFileReference(index),
        }
    }

    pub fn execute_db_type_allocation_todo(i_s: &InferenceState<'db, '_>, t: &Type) -> Self {
        // Everything that calls this should probably not allocate.
        let t = t.as_db_type();
        Self::from_type(t)
    }

    pub fn from_type(t: DbType) -> Self {
        Self {
            state: InferredState::UnsavedComplex(ComplexPoint::TypeInstance(t)),
        }
    }

    pub fn execute_db_type(i_s: &InferenceState<'db, '_>, generic: DbType) -> Self {
        let state = match generic {
            DbType::Type(ref c)
                if matches!(
                    c.as_ref(),
                    DbType::Class(GenericClass {
                        generics: ClassGenerics::None,
                        ..
                    })
                ) =>
            {
                match c.as_ref() {
                    DbType::Class(c) => {
                        let node_ref = NodeRef::from_link(i_s.db, c.link);
                        InferredState::Saved(c.link)
                    }
                    _ => unreachable!(),
                }
            }
            DbType::None => return Inferred::new_none(),
            DbType::Any => return Inferred::new_any(),
            _ => InferredState::UnsavedComplex(ComplexPoint::TypeInstance(generic)),
        };
        Self { state }
    }

    pub fn saved_as_type(&self, i_s: &InferenceState<'db, '_>) -> Option<Type<'db>> {
        match &self.state {
            InferredState::Saved(definition) => Some(saved_as_type(i_s, *definition)),
            _ => None,
        }
    }

    pub fn as_type(&'slf self, i_s: &InferenceState<'db, '_>) -> Type<'slf> {
        match &self.state {
            InferredState::Saved(definition) => saved_as_type(i_s, *definition),
            InferredState::UnsavedComplex(complex) => type_of_complex(i_s, complex, None),
            InferredState::UnsavedSpecific(specific) => match specific {
                Specific::None => Type::new(&DbType::None),
                Specific::Any | Specific::Cycle => Type::new(&DbType::Any),
                _ => unreachable!("{specific:?}"),
            },
            InferredState::UnsavedFileReference(file_index) => {
                Type::owned(DbType::Module(*file_index))
            }
            InferredState::BoundMethod {
                instance,
                mro_index,
                func_link,
            } => {
                let class = Self::load_bound_method_class(i_s, instance, *mro_index);
                load_bound_method(i_s, instance, class, *func_link).as_type(i_s)
            }
            InferredState::Unknown => Type::new(&DbType::Any),
        }
    }

    pub fn as_db_type(&self, i_s: &InferenceState<'db, '_>) -> DbType {
        self.as_type(i_s).into_db_type()
    }

    pub fn format(&self, i_s: &InferenceState<'db, '_>, format_data: &FormatData) -> Box<str> {
        self.as_type(i_s).format(format_data)
    }

    pub fn format_short(&self, i_s: &InferenceState<'db, '_>) -> Box<str> {
        self.format(i_s, &FormatData::new_short(i_s.db))
    }

    fn load_bound_method_class(
        i_s: &InferenceState<'db, '_>,
        instance: &'slf DbType,
        mro_index: MroIndex,
    ) -> Class<'slf> {
        let instance_class = match instance {
            DbType::Class(c) => Class::from_generic_class(i_s.db, c),
            DbType::Type(t) => match t.as_ref() {
                DbType::Class(c) => {
                    let c = Class::from_generic_class(i_s.db, c);
                    c.use_cached_class_infos(i_s.db).metaclass(i_s.db)
                }
                _ => unreachable!(),
            },
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
            TypeOrClass::Type(t) => match t.expect_borrowed_db_type() {
                DbType::Dataclass(d) => Class::from_generic_class(i_s.db, &d.class),
                DbType::TypedDict(d) => todo!("is this even necessary?"),
                _ => unreachable!(),
            },
        }
    }
    pub fn maybe_type_var_like(&self, i_s: &InferenceState<'db, '_>) -> Option<TypeVarLike> {
        if let InferredState::Saved(definition) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::TypeVarLike(t)) = node_ref.complex() {
                return Some(t.clone());
            }
        }
        None
    }

    pub fn maybe_new_type(&self, i_s: &InferenceState) -> Option<Rc<NewType>> {
        if let InferredState::Saved(definition) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::NewTypeDefinition(n)) = node_ref.complex() {
                return Some(n.clone());
            }
        }
        None
    }

    pub fn maybe_named_tuple_definition(&self, i_s: &InferenceState) -> Option<DbType> {
        if let InferredState::Saved(definition) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::NamedTupleDefinition(n)) = node_ref.complex() {
                return Some(n.as_ref().clone());
            }
        }
        None
    }

    pub fn maybe_typed_dict_definition(&self, i_s: &InferenceState) -> Option<DbType> {
        if let InferredState::Saved(definition) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::TypedDictDefinition(n)) = node_ref.complex() {
                return Some(n.as_ref().clone());
            }
        }
        None
    }

    pub fn maybe_enum_definition(&self, i_s: &InferenceState) -> Option<Rc<Enum>> {
        if let InferredState::Saved(definition) = self.state {
            let node_ref = NodeRef::from_link(i_s.db, definition);
            if let Some(ComplexPoint::TypeInstance(DbType::Type(t))) = node_ref.complex() {
                if let DbType::Enum(e) = t.as_ref() {
                    return Some(e.clone());
                }
            }
        }
        None
    }

    pub fn maybe_saved_link(&self) -> Option<PointLink> {
        match self.state {
            InferredState::Saved(definition) => Some(definition),
            _ => None,
        }
    }

    pub fn maybe_saved_specific(&self, db: &Database) -> Option<Specific> {
        self.maybe_saved_link()
            .and_then(|link| NodeRef::from_link(db, link).point().maybe_specific())
    }

    pub fn resolve_untyped_function_return(self, i_s: &InferenceState<'db, '_>) -> Self {
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
        i_s: &InferenceState<'db, '_>,
        class: &Class,
        attribute_class: &Class,
    ) -> Self {
        if attribute_class.has_simple_self_generics() {
            return self;
        }
        if let InferredState::Saved(link) = self.state {
            let definition = NodeRef::from_link(i_s.db, link);
            if let Some(specific) = definition.point().maybe_specific() {
                match specific {
                    Specific::Closure => {
                        todo!()
                    }
                    Specific::Param | Specific::MaybeSelfParam => {
                        todo!("might not even happen - remove")
                        //return i_s.infer_param(&definition);
                    }
                    Specific::AnnotationOrTypeCommentWithTypeVars => {
                        let t = use_cached_annotation_or_type_comment(i_s, definition);
                        let d =
                            replace_class_type_vars(i_s.db, t.as_ref(), attribute_class, &|| {
                                class.as_db_type(i_s.db)
                            });
                        return Inferred::from_type(d);
                    }
                    _ => (),
                }
            }
        }
        self
    }

    pub fn expect_class_or_simple_generic(&self, i_s: &InferenceState<'db, '_>) -> Type<'db> {
        let mut generics = ClassGenerics::None;
        if let InferredState::Saved(link) = &self.state {
            let definition = NodeRef::from_link(i_s.db, *link);
            let point = definition.point();
            if point.type_() == PointType::Specific {
                generics = Self::expect_class_generics(definition, point);
            }
        }
        let link = self.get_class_link(i_s);
        Type::owned(DbType::new_class(link, generics))
    }

    fn get_class_link(&self, i_s: &InferenceState) -> PointLink {
        let InferredState::Saved(link) = &self.state else {
            unreachable!()
        };
        let node_ref = NodeRef::from_link(i_s.db, *link);
        let point = node_ref.point();
        match point.type_() {
            PointType::Complex => {
                let complex = node_ref.file.complex_points.get(point.complex_index());
                let ComplexPoint::Class(c) = complex else {
                    unreachable!();
                };
                *link
            }
            PointType::Specific => match point.specific() {
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
        }
        if let Some(ComplexPoint::TypeInstance(t)) = self.maybe_complex_point(db) {
            match t {
                DbType::Union(t) => match t.iter().next() {
                    Some(DbType::Literal(_)) => {
                        UnionValue::Multiple(t.iter().map_while(|t| match t {
                            DbType::Literal(literal) => Some(literal.clone()),
                            _ => None,
                        }))
                    }
                    _ => UnionValue::Any,
                },
                DbType::Literal(literal) => UnionValue::Single(literal.clone()),
                _ => UnionValue::Any,
            }
        } else {
            UnionValue::Any
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
        if let DbType::Literal(DbLiteral {
            kind: LiteralKind::Bool(b),
            ..
        }) = self.as_type(i_s).as_ref()
        {
            Some(*b)
        } else {
            None
        }
    }

    pub fn maybe_string_literal(&self, i_s: &InferenceState) -> Option<DbString> {
        if let DbType::Literal(DbLiteral {
            kind: LiteralKind::String(b),
            ..
        }) = self.as_type(i_s).as_ref()
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
            InferredState::UnsavedComplex(complex) => {
                file.complex_points
                    .insert(&file.points, index, complex, Locality::Todo);
                return Self::new_saved(file, index);
            }
            InferredState::UnsavedSpecific(mut specific) => {
                if specific == Specific::Cycle {
                    let r = NodeRef::new(file, index);
                    r.add_issue(
                        i_s,
                        IssueType::CyclicDefinition {
                            name: Box::from(r.as_code()),
                        },
                    );
                    specific = Specific::Any;
                }
                Point::new_simple_specific(specific, Locality::Todo)
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
                    ComplexPoint::TypeInstance(bound_method.as_type(i_s).into_db_type()),
                    Locality::Todo,
                );
                return Self::new_saved(file, index);
            }
            InferredState::Unknown => Point::new_unknown(Locality::Todo),
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
                    Some(Specific::DecoratedFunction) => {
                        return Function::new(definition, class)
                            .decorated(i_s)
                            .init_as_function(i_s, class)
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
                    Some(ComplexPoint::TypeInstance(DbType::Callable(c))) => {
                        return Some(FunctionOrOverload::Callable(c.clone()));
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(DbType::Callable(c))) => {
                return Some(FunctionOrOverload::Callable(c.clone()));
            }
            _ => (),
        }
        None
    }

    #[inline]
    pub fn gather_types_union(
        callable: impl FnOnce(&mut dyn FnMut(&InferenceState<'db, '_>, Self)),
    ) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |i_s, inferred| {
            *r = Some(match r.take() {
                Some(i) => i.types_union(i_s, inferred, &mut ResultContext::Unknown),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| todo!())
    }

    pub fn types_union(
        self,
        i_s: &InferenceState<'db, '_>,
        other: Self,
        result_context: &mut ResultContext,
    ) -> Self {
        if result_context.expects_union(i_s) || self.is_union(i_s) || other.is_union(i_s) {
            self.union(i_s, other)
        } else {
            let second = other.as_type(i_s);
            let t = self.as_type(i_s).common_base_type(i_s, &second);
            Inferred::from_type(t)
        }
    }

    pub fn union(self, i_s: &InferenceState, other: Self) -> Self {
        if self.state == other.state {
            self
        } else {
            Inferred::from_type(
                self.as_type(i_s)
                    .union(i_s.db, other.as_type(i_s))
                    .into_db_type(),
            )
        }
    }

    #[inline]
    pub fn gather_union(i_s: &InferenceState, callable: impl FnOnce(&mut dyn FnMut(Self))) -> Self {
        let mut result: Option<Self> = None;
        let r = &mut result;
        callable(&mut |inferred| {
            *r = Some(match r.take() {
                Some(i) => i.union(i_s, inferred),
                None => inferred,
            });
        });
        result.unwrap_or_else(|| todo!())
    }

    pub fn bind_instance_descriptors(
        self,
        i_s: &InferenceState<'db, '_>,
        instance: DbType,
        func_class: Class,
        from: NodeRef,
        mro_index: MroIndex,
    ) -> Option<Self> {
        self.bind_instance_descriptors_internal(
            i_s,
            instance,
            func_class,
            from,
            mro_index,
            ApplyDescriptorsKind::All,
        )
    }

    fn bind_instance_descriptors_internal(
        self,
        i_s: &InferenceState<'db, '_>,
        instance: DbType,
        attribute_class: Class,
        from: NodeRef,
        mro_index: MroIndex,
        apply_descriptors_kind: ApplyDescriptorsKind,
    ) -> Option<Self> {
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.type_() {
                    PointType::Specific => match point.specific() {
                        Specific::Function => {
                            let func = prepare_func(i_s, *definition, attribute_class);
                            return if let Some(first_type) = func.first_param_annotation_type(i_s) {
                                if let Some(t) = create_signature_without_self(
                                    i_s,
                                    Matcher::new_function_matcher(func, func.type_vars(i_s)),
                                    || {
                                        func.as_callable(
                                            i_s,
                                            FirstParamProperties::Skip {
                                                to_self_instance: &|| instance.clone(),
                                            },
                                        )
                                    },
                                    &instance,
                                    &attribute_class,
                                    first_type.as_ref(),
                                ) {
                                    Some(Self::new_unsaved_complex(ComplexPoint::TypeInstance(
                                        DbType::Callable(Rc::new(t)),
                                    )))
                                } else {
                                    let t = IssueType::InvalidSelfArgument {
                                        argument_type: instance.format_short(i_s.db),
                                        function_name: Box::from(func.name()),
                                        callable: func.as_type(i_s).format_short(i_s.db),
                                    };
                                    from.add_issue(i_s, t);
                                    Some(Self::new_any())
                                }
                            } else {
                                Some(Self::new_bound_method(instance, mro_index, *definition))
                            };
                        }
                        Specific::DecoratedFunction => {
                            let func = prepare_func(i_s, *definition, attribute_class);
                            return func.decorated(i_s).bind_instance_descriptors_internal(
                                i_s,
                                instance,
                                attribute_class,
                                from,
                                mro_index,
                                // Class vars are remapped separatly
                                apply_descriptors_kind,
                            );
                        }
                        // TODO this should have the case of Specific::AnnotationOrTypeCommentClassVar as well
                        Specific::AnnotationOrTypeCommentWithTypeVars
                            if !attribute_class.has_simple_self_generics() =>
                        {
                            let t = use_cached_annotation_or_type_comment(i_s, node_ref);
                            let t = replace_class_type_vars(
                                i_s.db,
                                t.as_ref(),
                                &attribute_class,
                                &|| instance.clone(),
                            );
                            return Inferred::from_type(t).bind_instance_descriptors_internal(
                                i_s,
                                instance,
                                attribute_class,
                                from,
                                mro_index,
                                ApplyDescriptorsKind::NoBoundMethod,
                            );
                        }
                        specific @ (Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance
                        | Specific::AnnotationOrTypeCommentClassVar) => {
                            let t = use_cached_annotation_or_type_comment(i_s, node_ref);
                            if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                i_s,
                                instance,
                                attribute_class,
                                from,
                                mro_index,
                                None,
                                t.as_ref(),
                                if specific == Specific::AnnotationOrTypeCommentClassVar {
                                    ApplyDescriptorsKind::All
                                } else {
                                    ApplyDescriptorsKind::NoBoundMethod
                                },
                            ) {
                                return inf;
                            }
                        }
                        _ => (),
                    },
                    PointType::Complex => {
                        let file = i_s.db.loaded_python_file(definition.file);
                        match file.complex_points.get(point.complex_index()) {
                            ComplexPoint::FunctionOverload(o) => {
                                let has_self_arguments = o.iter_functions().any(|c| {
                                    Function::new(
                                        NodeRef::from_link(i_s.db, c.defined_at),
                                        Some(attribute_class),
                                    )
                                    .first_param_annotation_type(i_s)
                                    .is_some()
                                });
                                if has_self_arguments {
                                    let results: Vec<_> = o
                                        .iter_functions()
                                        .filter_map(|callable| {
                                            if let Some(t) = callable.first_positional_type() {
                                                create_signature_without_self_for_callable(
                                                    i_s,
                                                    callable,
                                                    &instance,
                                                    &attribute_class,
                                                    t,
                                                )
                                            } else {
                                                todo!()
                                            }
                                        })
                                        .collect();
                                    match results.len() {
                                        0 => {
                                            let overload = OverloadedFunction::new(
                                                &o.functions,
                                                Some(attribute_class),
                                            );
                                            let t = IssueType::InvalidClassMethodFirstArgument {
                                                argument_type: DbType::Type(Rc::new(instance))
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
                                            from.add_issue(i_s, t);
                                            return Some(Self::new_any());
                                        }
                                        1 => {
                                            return Some(Inferred::from_type(DbType::Callable(
                                                Rc::new(results.into_iter().next().unwrap()),
                                            )));
                                        }
                                        _ => {
                                            return Some(Inferred::from_type(
                                                DbType::FunctionOverload(FunctionOverload::new(
                                                    results.into_iter().collect(),
                                                )),
                                            ));
                                        }
                                    }
                                }
                                return Some(Self::new_bound_method(
                                    instance,
                                    mro_index,
                                    *definition,
                                ));
                            }
                            ComplexPoint::TypeInstance(t) => {
                                if let Some(inf) = Self::bind_instance_descriptors_for_type(
                                    i_s,
                                    instance,
                                    attribute_class,
                                    from,
                                    mro_index,
                                    Some(*definition),
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
                        instance,
                        attribute_class,
                        from,
                        mro_index,
                        None,
                        t,
                        apply_descriptors_kind,
                    ) {
                        return inf;
                    }
                }
            }
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::BoundMethod { .. } => todo!(),
            InferredState::Unknown => (),
        }
        Some(self)
    }

    fn bind_instance_descriptors_for_type(
        i_s: &InferenceState<'db, '_>,
        instance: DbType,
        attribute_class: Class,
        from: NodeRef,
        mro_index: MroIndex,
        definition: Option<PointLink>,
        t: &DbType,
        apply_descriptors_kind: ApplyDescriptorsKind,
    ) -> Option<Option<Self>> {
        let mut t = t; // Weird lifetime issue
        if let DbType::Callable(c) = t {
            match c.kind {
                FunctionKind::Function
                    if !matches!(apply_descriptors_kind, ApplyDescriptorsKind::NoBoundMethod) =>
                {
                    debug_assert_eq!(c.kind, FunctionKind::Function);
                    if let Some(f) = c.first_positional_type() {
                        return Some(
                            create_signature_without_self_for_callable(
                                i_s,
                                c,
                                &instance,
                                &attribute_class,
                                f,
                            )
                            .map(|c| Inferred::from_type(DbType::Callable(Rc::new(c)))),
                        );
                    } else {
                        todo!()
                    }
                }
                FunctionKind::Function => (),
                FunctionKind::Property { .. } => {
                    let first = c.first_positional_type();
                    return Some(Some(
                        if let Some(t) =
                            calculate_property_return(i_s, &instance, &attribute_class, c)
                        {
                            Inferred::from_type(t)
                        } else {
                            let inv = IssueType::InvalidSelfArgument {
                                argument_type: instance.format_short(i_s.db),
                                function_name: Box::from(
                                    c.name.map(|n| n.as_str(i_s.db)).unwrap_or(""),
                                ),
                                callable: c.format(&FormatData::new_short(i_s.db)).into(),
                            };
                            from.add_issue(i_s, inv);
                            Inferred::new_any()
                        },
                    ));
                }
                FunctionKind::Classmethod => {
                    let DbType::Class(instance_cls) = &instance else {
                        todo!("Is this always the case?")
                    };
                    let instance_cls = Class::from_generic_class(i_s.db, instance_cls);
                    let result = infer_class_method(i_s, instance_cls, attribute_class, c);
                    if result.is_none() {
                        let func = prepare_func(i_s, c.defined_at, attribute_class);
                        let t = IssueType::InvalidClassMethodFirstArgument {
                            argument_type: DbType::Type(Rc::new(instance)).format_short(i_s.db),
                            function_name: Box::from(func.name()),
                            callable: func.as_type(i_s).format_short(i_s.db),
                        };
                        from.add_issue(i_s, t);
                        return Some(Some(Self::new_any()));
                    }
                    return Some(result.map(callable_into_inferred));
                }
                // Static methods can be passed out without any remapping.
                FunctionKind::Staticmethod => (),
            }
        }

        let mut new = None;
        if !attribute_class.has_simple_self_generics() {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| instance.clone(),
            ));
            t = new.as_ref().unwrap();
        }

        if let DbType::Class(c) = t {
            let potential_descriptor = use_instance_with_ref(
                NodeRef::from_link(i_s.db, c.link),
                Generics::from_class_generics(i_s.db, &c.generics),
                None,
            );
            if let Some(inf) = potential_descriptor.bind_dunder_get(i_s, from, instance) {
                return Some(Some(inf));
            }
        }
        if let Some(new) = new {
            return Some(Some(Inferred::from_type(new)));
        }
        None
    }

    pub fn bind_class_descriptors(
        self,
        i_s: &InferenceState<'db, '_>,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        from: NodeRef,
        apply_descriptor: bool,
    ) -> Option<Self> {
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.type_() {
                    PointType::Specific => match point.specific() {
                        Specific::Function => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            let t =
                                func.as_db_type(i_s, FirstParamProperties::MethodAccessedOnClass);
                            return Some(Inferred::from_type(t));
                        }
                        Specific::DecoratedFunction => {
                            return Function::new(node_ref, Some(attribute_class))
                                .decorated(i_s)
                                .bind_class_descriptors(
                                    i_s,
                                    class,
                                    attribute_class,
                                    from,
                                    apply_descriptor,
                                );
                        }
                        specific @ (Specific::AnnotationOrTypeCommentWithoutTypeVars
                        | Specific::AnnotationOrTypeCommentClassVar
                        | Specific::AnnotationOrTypeCommentWithTypeVars
                        | Specific::AnnotationOrTypeCommentSimpleClassInstance) => {
                            if specific == Specific::AnnotationOrTypeCommentWithTypeVars
                                && apply_descriptor
                            {
                                from.add_issue(i_s, IssueType::AmbigousClassVariableAccess);
                            }
                            let mut t = use_cached_annotation_or_type_comment(
                                i_s,
                                NodeRef::from_link(i_s.db, *definition),
                            );
                            let has_explicit_self = t.has_explicit_self_type(i_s.db);
                            if has_explicit_self {
                                t = Type::owned(replace_class_type_vars(
                                    i_s.db,
                                    t.as_ref(),
                                    &attribute_class,
                                    &|| class.as_db_type(i_s.db),
                                ));
                            }
                            if let Some(r) = Self::bind_class_descriptors_for_type(
                                i_s,
                                class,
                                attribute_class,
                                from,
                                apply_descriptor,
                                *definition,
                                t.as_ref(),
                            ) {
                                return r;
                            }
                            if has_explicit_self {
                                return Some(Inferred::from_type(t.into_db_type()));
                            }
                        }
                        _ => (),
                    },
                    PointType::Complex => {
                        let file = i_s.db.loaded_python_file(definition.file);
                        match file.complex_points.get(point.complex_index()) {
                            ComplexPoint::FunctionOverload(o) => match o.kind() {
                                FunctionKind::Function => {
                                    return Some(Inferred::from_type(DbType::FunctionOverload(
                                        FunctionOverload::new(
                                            o.iter_functions()
                                                .map(|c| {
                                                    merge_class_type_vars_into_callable(
                                                        i_s.db,
                                                        *class,
                                                        attribute_class,
                                                        c,
                                                    )
                                                })
                                                .collect(),
                                        ),
                                    )))
                                }
                                FunctionKind::Property { .. } => unreachable!(),
                                FunctionKind::Classmethod => {
                                    return Some(infer_overloaded_class_method(
                                        i_s,
                                        *class,
                                        attribute_class,
                                        o,
                                    ))
                                }
                                FunctionKind::Staticmethod => (),
                            },
                            ComplexPoint::TypeInstance(t) => {
                                if let Some(r) = Self::bind_class_descriptors_for_type(
                                    i_s,
                                    class,
                                    attribute_class,
                                    from,
                                    apply_descriptor,
                                    *definition,
                                    t,
                                ) {
                                    return r;
                                }
                            }
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(complex) => (),
            InferredState::UnsavedSpecific(specific) => todo!(),
            InferredState::UnsavedFileReference(file_index) => todo!(),
            InferredState::BoundMethod { .. } => todo!(),
            InferredState::Unknown => (),
        }
        Some(self)
    }

    pub fn bind_class_descriptors_for_type(
        i_s: &InferenceState<'db, '_>,
        class: &Class,
        attribute_class: Class, // The (sub-)class in which an attribute is defined
        from: NodeRef,
        apply_descriptor: bool,
        definition: PointLink,
        t: &DbType,
    ) -> Option<Option<Self>> {
        let mut t = t;
        if let DbType::Callable(c) = t {
            match c.kind {
                FunctionKind::Function => (),
                FunctionKind::Property { .. } => {
                    return Some(Some(Inferred::from_type(
                        i_s.db.python_state.property_db_type(),
                    )))
                }
                FunctionKind::Classmethod => {
                    let result = infer_class_method(i_s, *class, attribute_class, c);
                    if result.is_none() {
                        let func = prepare_func(i_s, c.defined_at, attribute_class);
                        let inv = IssueType::InvalidSelfArgument {
                            argument_type: class.as_type(i_s).format_short(i_s.db),
                            function_name: Box::from(func.name()),
                            callable: func.as_type(i_s).format_short(i_s.db),
                        };
                        from.add_issue(i_s, inv);
                        return Some(Some(Self::new_any()));
                    }
                    return Some(result.map(callable_into_inferred));
                }
                FunctionKind::Staticmethod => (),
            }
        }
        let needs_remapping = match attribute_class.generics {
            Generics::Self_ { .. } => !attribute_class.has_simple_self_generics(),
            _ => !attribute_class.type_vars(i_s).is_empty(),
        };
        let mut new = None;
        if needs_remapping {
            new = Some(replace_class_type_vars(
                i_s.db,
                t,
                &attribute_class,
                &|| class.as_db_type(i_s.db),
            ));
            t = new.as_ref().unwrap();
        }

        if let DbType::Class(c) = t {
            if apply_descriptor {
                let inst = use_instance_with_ref(
                    NodeRef::from_link(i_s.db, c.link),
                    Generics::from_class_generics(i_s.db, &c.generics),
                    None,
                );
                if let Some(inf) = inst.type_lookup(i_s, from, "__get__").into_maybe_inferred() {
                    let class_as_inferred = class.as_inferred(i_s);
                    return Some(Some(inf.execute(
                        i_s,
                        &CombinedArguments::new(
                            &KnownArguments::new(&Inferred::new_none(), from),
                            &KnownArguments::new(&class_as_inferred, from),
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
        i_s: &InferenceState<'db, '_>,
        class: &Class,
        class_of_attribute: Option<Class>,
    ) -> Self {
        // This method exists for __new__
        let attribute_class = class_of_attribute.unwrap_or(*class);
        match &self.state {
            InferredState::Saved(definition) => {
                let node_ref = NodeRef::from_link(i_s.db, *definition);
                let point = node_ref.point();
                match point.type_() {
                    PointType::Specific => match point.specific() {
                        Specific::Function => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            let result = infer_class_method(
                                i_s,
                                *class,
                                attribute_class,
                                &func.as_callable(i_s, FirstParamProperties::None),
                            );
                            if let Some(result) = result {
                                return callable_into_inferred(result);
                            } else {
                                todo!()
                            }
                        }
                        Specific::DecoratedFunction => {
                            let func = Function::new(node_ref, Some(attribute_class));
                            return func.decorated(i_s).bind_new_descriptors(
                                i_s,
                                class,
                                class_of_attribute,
                            );
                        }
                        _ => (),
                    },
                    PointType::Complex => {
                        let file = i_s.db.loaded_python_file(definition.file);
                        match file.complex_points.get(point.complex_index()) {
                            ComplexPoint::FunctionOverload(o) => {
                                return infer_overloaded_class_method(
                                    i_s,
                                    *class,
                                    attribute_class,
                                    o,
                                )
                            }
                            ComplexPoint::TypeInstance(DbType::Callable(_)) => todo!(),
                            _ => (),
                        }
                    }
                    _ => (),
                }
            }
            InferredState::UnsavedComplex(ComplexPoint::TypeInstance(DbType::Callable(c))) => {
                // This is reached by NamedTuples. Not sure it this reached otherwise as well.
                let result = infer_class_method(i_s, *class, attribute_class, c);
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
            InferredState::Unknown => (),
        }
        self
    }

    pub fn debug_info(&self, i_s: &InferenceState<'db, '_>) -> String {
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

    fn expect_class_generics(definition: NodeRef<'db>, point: Point) -> ClassGenerics {
        debug_assert_eq!(point.type_(), PointType::Specific);
        debug_assert_eq!(point.specific(), Specific::SimpleGeneric);
        let PrimaryContent::GetItem(slice_type) = definition.as_primary().second() else {
            unreachable!();
        };
        match slice_type {
            ASTSliceType::NamedExpression(named) => ClassGenerics::ExpressionWithClassType(
                PointLink::new(definition.file_index(), named.expression().index()),
            ),
            ASTSliceType::Slice(_) => unreachable!(),
            ASTSliceType::Slices(slices) => ClassGenerics::SlicesWithClassTypes(PointLink::new(
                definition.file_index(),
                slices.index(),
            )),
        }
    }

    pub fn is_union(&self, i_s: &InferenceState) -> bool {
        let check_complex_point = |c: &_| match c {
            ComplexPoint::TypeInstance(t) => Type::new(t).is_union(),
            _ => false,
        };
        match &self.state {
            InferredState::Saved(reference) => {
                let node_ref = NodeRef::from_link(i_s.db, *reference);
                let point = node_ref.point();
                if point.type_() == PointType::Specific {
                    if matches!(
                        point.specific(),
                        Specific::AnnotationOrTypeCommentWithTypeVars
                            | Specific::AnnotationOrTypeCommentWithoutTypeVars
                            | Specific::AnnotationOrTypeCommentSimpleClassInstance
                    ) {
                        use_cached_annotation_or_type_comment(i_s, node_ref).is_union()
                    } else {
                        // TODO the node_ref may not be an annotation.
                        false
                    }
                } else {
                    node_ref.complex().is_some_and(|c| check_complex_point(c))
                }
            }
            InferredState::UnsavedComplex(c) => check_complex_point(c),
            _ => false,
        }
    }

    #[inline]
    pub fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        kind: LookupKind,
        callable: &mut impl FnMut(&Type, LookupResult),
    ) {
        self.as_type(i_s).run_after_lookup_on_each_union_member(
            i_s,
            Some(self),
            from,
            name,
            kind,
            &mut ResultContext::Unknown,
            callable,
        )
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        self.lookup_with_result_context(i_s, node_ref, name, kind, &mut ResultContext::Unknown)
    }

    pub fn lookup_with_result_context(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
    ) -> LookupResult {
        let base_type = self.as_type(i_s);
        base_type.lookup(i_s, node_ref, name, kind, result_context, &|t| {
            add_attribute_error(i_s, node_ref, &base_type, t, name)
        })
    }

    pub fn type_lookup_and_execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        args: &dyn Arguments<'db>,
        on_lookup_error: OnLookupError,
    ) -> Self {
        self.type_lookup_and_execute_with_details(
            i_s,
            from,
            name,
            args,
            on_lookup_error,
            OnTypeError::new(&on_argument_type_error),
        )
    }

    pub fn type_lookup_and_execute_with_attribute_error(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        args: &dyn Arguments<'db>,
    ) -> Self {
        self.type_lookup_and_execute(i_s, from, name, args, &|t| {
            add_attribute_error(i_s, from, &self.as_type(i_s), t, name)
        })
    }

    pub fn type_lookup_and_execute_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        from: NodeRef,
        name: &str,
        args: &dyn Arguments<'db>,
        on_lookup_error: OnLookupError,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Self {
        let mut result: Option<Inferred> = None;
        self.run_after_lookup_on_each_union_member(
            i_s,
            from,
            name,
            LookupKind::OnlyType,
            &mut |_, lookup_result| {
                if matches!(lookup_result, LookupResult::None) {
                    on_lookup_error(&self.as_type(i_s));
                }
                let inf = lookup_result.into_inferred().execute_with_details(
                    i_s,
                    args,
                    &mut ResultContext::ExpectUnused,
                    on_type_error,
                );
                result = if let Some(r) = result.take() {
                    Some(r.union(i_s, inf))
                } else {
                    Some(inf)
                }
            },
        );
        result.unwrap_or_else(|| todo!())
    }

    pub fn execute(&self, i_s: &InferenceState<'db, '_>, args: &dyn Arguments<'db>) -> Self {
        self.execute_with_details(
            i_s,
            args,
            &mut ResultContext::Unknown,
            OnTypeError::new(&on_argument_type_error),
        )
    }

    pub fn execute_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Arguments<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError<'db, '_>,
    ) -> Self {
        match &self.state {
            InferredState::Saved(link) => {
                let node_ref = NodeRef::from_link(i_s.db, *link);
                let point = node_ref.point();
                match point.type_() {
                    PointType::Specific => {
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
                            Specific::TypingTypeVarClass => {
                                return TypeVarClass().execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingTypeVarTupleClass => {
                                return TypeVarTupleClass().execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingParamSpecClass => {
                                return ParamSpecClass().execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingProtocol
                            | Specific::TypingGeneric
                            | Specific::TypingUnion
                            | Specific::TypingOptional
                            | Specific::TypingLiteral
                            | Specific::TypingAnnotated
                            | Specific::TypingCallable => todo!(),
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
                                todo!()
                            }
                            Specific::TypingCast => {
                                return TypingCast().execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::RevealTypeFunction => {
                                return RevealTypeFunction().execute(
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
                                return NewTypeClass().execute(
                                    i_s,
                                    args,
                                    result_context,
                                    on_type_error,
                                )
                            }
                            Specific::TypingAny => {
                                args.as_node_ref().add_issue(i_s, IssueType::AnyNotCallable);
                                args.iter().calculate_diagnostics(i_s);
                                return Inferred::new_any();
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
                            _ => (),
                        }
                    }
                    PointType::Complex => {
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
                                return Class::new(node_ref, cls, Generics::NotDefinedYet, None)
                                    .execute(i_s, args, result_context, on_type_error)
                            }
                            ComplexPoint::TypeAlias(alias) => {
                                if alias.is_class() {
                                    return Inferred::from_type(
                                        alias.as_db_type_and_set_type_vars_any(i_s.db),
                                    );
                                }
                                args.as_node_ref().add_issue(
                                    i_s,
                                    IssueType::NotCallable {
                                        type_: Box::from("\"<typing special form>\""),
                                    },
                                );
                                return Inferred::new_any();
                            }
                            ComplexPoint::NewTypeDefinition(new_type) => {
                                let mut iterator = args.iter();
                                if let Some(first_arg) = iterator.next() {
                                    let t = Type::new(new_type.type_(i_s));
                                    let inf = first_arg.infer(i_s, &mut ResultContext::Known(&t));
                                    t.error_if_not_matches(i_s, &inf, |t1, t2| {
                                        (on_type_error.callback)(
                                            i_s,
                                            &|_| {
                                                Some(
                                                    format!(" to \"{}\"", new_type.name(i_s.db))
                                                        .into(),
                                                )
                                            },
                                            &first_arg,
                                            t1,
                                            t2,
                                        );
                                        args.as_node_ref().to_db_lifetime(i_s.db)
                                    });
                                } else {
                                    args.as_node_ref().add_issue(
                                        i_s,
                                        IssueType::TooFewArguments(
                                            format!(" for \"{}\"", new_type.name(i_s.db)).into(),
                                        ),
                                    );
                                }
                                if iterator.next().is_some() {
                                    args.as_node_ref().add_issue(
                                        i_s,
                                        IssueType::TooManyArguments(
                                            format!(" for \"{}\"", new_type.name(i_s.db)).into(),
                                        ),
                                    );
                                }
                                return Self::from_type(DbType::NewType(new_type.clone()));
                            }
                            _ => (),
                        }
                    }
                    PointType::FileReference => {
                        args.as_node_ref().add_issue(
                            i_s,
                            IssueType::NotCallable {
                                type_: Box::from("Module"),
                            },
                        );
                        return Inferred::new_unknown();
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
        self.as_type(i_s)
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
                    return slice_type
                        .file
                        .inference(i_s)
                        .compute_type_application_on_typing_class(
                            specific,
                            *slice_type,
                            matches!(result_context, ResultContext::AssignmentNewDefinition),
                        )
                }
                Some(Specific::TypingClassVar) => {
                    return match slice_type.unpack() {
                        SliceTypeContent::Simple(simple) => {
                            // TODO if it is a (), it's am empty tuple
                            simple.infer(i_s, &mut ResultContext::Unknown)
                        }
                        SliceTypeContent::Slice(x) => {
                            todo!()
                        }
                        SliceTypeContent::Slices(x) => {
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
                        Some(ComplexPoint::Class(c)) => {
                            let class = Class::new(node_ref, c, Generics::NotDefinedYet, None);
                            return class.get_item(i_s, slice_type, result_context);
                        }
                        _ => (),
                    }
                }
            }
        }
        self.as_type(i_s)
            .get_item(i_s, Some(self), slice_type, result_context)
    }

    pub fn type_check_set_item(
        &self,
        i_s: &InferenceState<'db, '_>,
        slice_type: SliceType,
        from: NodeRef,
        value: &Inferred,
    ) {
        debug!("Set Item on {}", self.format_short(i_s));
        if let Some(typed_dict) = self.as_type(i_s).maybe_typed_dict(i_s.db) {
            if let Some(literal) = slice_type
                .infer_with_context(i_s, &mut ResultContext::ExpectLiteral)
                .maybe_string_literal(i_s)
            {
                let key = literal.as_str(i_s.db);
                if let Some(param) = typed_dict.find_param(i_s.db, key) {
                    Type::new(param.param_specific.expect_positional_db_type_as_ref())
                        .error_if_not_matches(i_s, &value, |got, expected| {
                            let node_ref = slice_type.as_node_ref();
                            node_ref.add_issue(
                                i_s,
                                IssueType::TypedDictKeySetItemIncompatibleType {
                                    key: key.into(),
                                    got,
                                    expected,
                                },
                            );
                            node_ref.to_db_lifetime(i_s.db)
                        });
                } else {
                    slice_type.as_node_ref().add_issue(
                        i_s,
                        IssueType::TypedDictHasNoKey {
                            typed_dict: self.format_short(i_s),
                            key: key.into(),
                        },
                    );
                }
            } else {
                TypedDictHelper(&typed_dict)
                    .add_access_key_must_be_string_literal_issue(i_s, slice_type.as_node_ref())
            }
            return;
        }
        let args = slice_type.as_args(*i_s);
        self.type_lookup_and_execute_with_details(
            i_s,
            from,
            "__setitem__",
            &CombinedArguments::new(&args, &KnownArguments::new(value, from)),
            &|_| {
                debug!("TODO __setitem__ not found");
            },
            OnTypeError::new(&|i_s, function, arg, got, expected| {
                let type_ = if arg.index == 1 {
                    IssueType::InvalidGetItem {
                        actual: got,
                        type_: self.format_short(i_s),
                        expected,
                    }
                } else {
                    IssueType::InvalidSetItemTarget { got, expected }
                };
                arg.as_node_ref().add_issue(i_s, type_)
            }),
        );
    }

    pub fn iter(self, i_s: &InferenceState<'db, '_>, from: NodeRef) -> IteratorContent {
        self.as_type(i_s).iter(i_s, from)
    }
}

fn load_bound_method<'db: 'a, 'a, 'b>(
    i_s: &InferenceState<'db, '_>,
    instance: &'b DbType,
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

fn resolve_specific(i_s: &InferenceState, specific: Specific) -> Type<'static> {
    // TODO this should be using python_state.str_node_ref etc.
    load_builtin_type_from_str(
        i_s,
        match specific {
            Specific::String | Specific::StringLiteral => "str",
            Specific::IntLiteral | Specific::Int => "int",
            Specific::Float => "float",
            Specific::BoolLiteral | Specific::Bool => {
                return Type::owned(i_s.db.python_state.bool_db_type())
            }
            Specific::BytesLiteral | Specific::Bytes => "bytes",
            Specific::Complex => "complex",
            Specific::Ellipsis => return Type::owned(i_s.db.python_state.ellipsis_db_type()),
            actual => unreachable!("{actual:?}"),
        },
    )
}

fn load_builtin_type_from_str(i_s: &InferenceState, name: &'static str) -> Type<'static> {
    let builtins = i_s.db.python_state.builtins();
    let node_index = builtins.lookup_global(name).unwrap().node_index - 1;
    // TODO this is slow and ugly, please make sure to do this different
    builtins
        .inference(i_s)
        .infer_name_definition(NodeRef::new(builtins, node_index).as_name_def());

    let v = builtins.points.get(node_index);
    debug_assert_eq!(v.type_(), PointType::Redirect);
    debug_assert_eq!(v.file_index(), builtins.file_index());
    Type::owned(DbType::new_class(
        PointLink::new(builtins.file_index(), v.node_index()),
        ClassGenerics::None,
    ))
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
    func.type_vars(i_s); // Cache annotations
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
) -> Inferred {
    Inferred::from_type(DbType::FunctionOverload(FunctionOverload::new(
        o.iter_functions()
            .map(|callable| {
                infer_class_method(i_s, class, attribute_class, callable).unwrap_or_else(|| todo!())
            })
            .collect(),
    )))
}

pub fn infer_class_method<'db: 'class, 'class>(
    i_s: &InferenceState<'db, '_>,
    mut class: Class<'class>,
    func_class: Class,
    callable: &CallableContent,
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
        &class,
        &func_class,
        class_generics_not_defined_yet,
    )
}

fn proper_classmethod_callable(
    i_s: &InferenceState,
    callable: &CallableContent,
    class: &Class,
    func_class: &Class,
    class_generics_not_defined_yet: bool,
) -> Option<CallableContent> {
    let mut class_method_type_var_usage = None;
    // TODO performance this clone might not be necessary.
    let mut callable = callable.clone();
    let mut type_vars = callable.type_vars.as_vec();
    match &callable.params {
        CallableParams::Simple(params) => {
            let mut vec = params.to_vec();
            // The first argument in a class param is not relevant if we execute descriptors.
            let first_param = vec.remove(0);

            if let Some(t) = first_param.param_specific.maybe_positional_db_type() {
                let mut matcher = Matcher::new_callable_matcher(&callable);
                let instance_t = class.as_type(i_s);
                let t =
                    replace_class_type_vars(i_s.db, t, func_class, &|| class.as_db_type(i_s.db));
                if !Type::new(&t)
                    .is_super_type_of(i_s, &mut matcher, &instance_t)
                    .bool()
                {
                    return None;
                }
                if let DbType::Type(t) = t {
                    if let DbType::TypeVar(usage) = t.as_ref() {
                        class_method_type_var_usage = Some(usage.clone());
                        type_vars.remove(0);
                    }
                }
            }
            callable.params = CallableParams::Simple(Rc::from(vec));
        }
        CallableParams::WithParamSpec(_, _) => todo!(),
        CallableParams::Any => (),
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
        if class_generics_not_defined_yet {
            let type_var_likes = class.use_cached_type_vars(i_s.db);
            DbType::new_class(
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
            class.as_db_type(i_s.db)
        }
    };
    let mut new_callable = Type::replace_type_var_likes_and_self_for_callable(
        &callable,
        i_s.db,
        &mut |mut usage| {
            let in_definition = usage.in_definition();
            if let Some(result) = maybe_class_usage(i_s.db, func_class, &usage) {
                // We need to remap again, because in generics of classes will be
                // generic in the function of the classmethod, see for example
                // `testGenericClassMethodUnboundOnClass`.
                if class_generics_not_defined_yet {
                    return result.replace_type_var_likes(
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
                        return GenericItem::TypeArgument(get_class_method_class());
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
    Some(new_callable)
}

fn callable_into_inferred(callable: CallableContent) -> Inferred {
    Inferred::from_type(DbType::Callable(Rc::new(callable)))
}

fn type_of_complex<'db: 'x, 'x>(
    i_s: &InferenceState<'db, '_>,
    complex: &'x ComplexPoint,
    definition: Option<NodeRef<'x>>,
) -> Type<'x> {
    match complex {
        ComplexPoint::Class(cls_storage) => {
            // This can only ever happen for saved definitions, therefore we can unwrap.
            Type::owned(DbType::Type(Rc::new(DbType::new_class(
                definition.unwrap().as_link(),
                ClassGenerics::NotDefinedYet,
            ))))
        }
        ComplexPoint::FunctionOverload(overload) => {
            let overload =
                OverloadedFunction::new(&overload.functions, i_s.current_class().copied());
            overload.as_type(i_s)
        }
        ComplexPoint::TypeInstance(t) => Type::new(t),
        // TODO is this type correct with the Any?
        ComplexPoint::TypeAlias(alias) => Type::owned(DbType::Type(Rc::new(
            alias.as_db_type_and_set_type_vars_any(i_s.db),
        ))),
        ComplexPoint::TypeVarLike(t) => match t {
            TypeVarLike::TypeVar(_) => i_s.db.python_state.type_var_type(),
            TypeVarLike::TypeVarTuple(_) => todo!(),
            TypeVarLike::ParamSpec(_) => todo!(),
        },
        ComplexPoint::NewTypeDefinition(n) => {
            Type::owned(DbType::Type(Rc::new(DbType::NewType(n.clone()))))
        }
        ComplexPoint::NamedTupleDefinition(n) => Type::owned(DbType::Type(n.clone())),
        ComplexPoint::TypedDictDefinition(t) => Type::owned(DbType::Type(t.clone())),
        _ => {
            unreachable!("Classes are handled earlier {complex:?}")
        }
    }
}

fn saved_as_type<'db>(i_s: &InferenceState<'db, '_>, definition: PointLink) -> Type<'db> {
    let definition = NodeRef::from_link(i_s.db, definition);
    let point = definition.point();
    match point.type_() {
        PointType::Specific => {
            let specific = point.specific();
            match specific {
                Specific::Any | Specific::Cycle => Type::new(&DbType::Any),
                Specific::IntLiteral => Type::owned(DbType::Literal(DbLiteral {
                    kind: LiteralKind::Int(definition.expect_int().parse().unwrap()),
                    implicit: true,
                })),
                Specific::StringLiteral => Type::owned(DbType::Literal(DbLiteral {
                    kind: LiteralKind::String(
                        DbString::from_python_string(
                            definition.file_index(),
                            definition.maybe_str().unwrap().as_python_string(),
                        )
                        .unwrap(),
                    ),
                    implicit: true,
                })),
                Specific::BoolLiteral => Type::owned(DbType::Literal(DbLiteral {
                    kind: LiteralKind::Bool(definition.as_code() == "True"),
                    implicit: true,
                })),
                Specific::BytesLiteral => Type::owned(DbType::Literal(DbLiteral {
                    kind: LiteralKind::Bytes(definition.as_link()),
                    implicit: true,
                })),
                Specific::Function => {
                    Function::new(definition, i_s.current_class().copied()).as_type(i_s)
                }
                Specific::DecoratedFunction => {
                    let func = Function::new(definition, i_s.current_class().copied());
                    // Caches the decorated inference properly
                    saved_as_type(i_s, func.decorated(i_s).maybe_saved_link().unwrap())
                }
                Specific::AnnotationOrTypeCommentSimpleClassInstance
                | Specific::AnnotationOrTypeCommentWithoutTypeVars
                | Specific::AnnotationOrTypeCommentWithTypeVars
                | Specific::AnnotationOrTypeCommentClassVar => {
                    use_cached_annotation_or_type_comment(i_s, definition)
                }
                Specific::MaybeSelfParam => Type::new(&DbType::Self_),
                Specific::TypingTypeVarClass => todo!(),
                Specific::TypingTypeVarTupleClass => todo!(),
                Specific::TypingParamSpecClass => todo!(),
                Specific::TypingType => Type::new(&i_s.db.python_state.type_of_any),
                Specific::TypingTuple => Type::new(&i_s.db.python_state.type_of_arbitrary_tuple),
                Specific::CollectionsNamedTuple => todo!(),
                Specific::TypingProtocol
                | Specific::TypingGeneric
                | Specific::TypingUnion
                | Specific::TypingOptional
                | Specific::TypingLiteral
                | Specific::TypingAnnotated
                | Specific::TypingNamedTuple
                | Specific::TypingTypedDict
                | Specific::TypingCallable => todo!(),
                Specific::TypingCast => todo!(),
                Specific::TypingClassVar => todo!(),
                Specific::RevealTypeFunction => todo!(),
                Specific::None => Type::new(&DbType::None),
                Specific::TypingNewType => todo!(),
                Specific::TypingAny => todo!(),
                Specific::MypyExtensionsArg
                | Specific::MypyExtensionsDefaultArg
                | Specific::MypyExtensionsNamedArg
                | Specific::MypyExtensionsDefaultNamedArg
                | Specific::MypyExtensionsVarArg
                | Specific::MypyExtensionsKwArg => {
                    i_s.db
                        .python_state
                        .mypy_extensions_arg_func(i_s.db, specific)
                        .as_type(i_s);
                    todo!()
                }
                _ => resolve_specific(i_s, specific),
            }
        }
        PointType::Complex => {
            let complex = definition.file.complex_points.get(point.complex_index());
            type_of_complex(i_s, complex, Some(definition))
        }
        PointType::FileReference => Type::owned(DbType::Module(point.file_index())),
        x => unreachable!("{x:?}"),
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
    let object = match t.as_ref() {
        DbType::Module(f) => {
            node_ref.add_issue(i_s, IssueType::ModuleAttributeError { name: name.into() });
            return;
        }
        _ => format!("{:?}", t.format_short(i_s.db)).into(),
    };
    let name = Box::from(name);
    if let DbType::TypeVar(usage) = full_type.as_ref() {
        if let TypeVarKind::Bound(bound) = &usage.type_var.kind {
            if Type::new(bound).is_union() {
                let bound = bound.format_short(i_s.db);
                let type_var_name = usage.type_var.name(i_s.db);
                node_ref.add_issue(
                    i_s,
                    IssueType::UnionAttributeErrorOfUpperBound(format!(
                        r#"Item {object} of the upper bound "{bound}" of type variable "{type_var_name}" has no attribute "{name}""#
                    ).into())
                );
                return;
            }
        }
    }
    node_ref.add_issue(
        i_s,
        match full_type.is_union() {
            false => IssueType::AttributeError { object, name },
            true => IssueType::UnionAttributeError {
                object,
                union: full_type.format_short(i_s.db),
                name,
            },
        },
    );
}
