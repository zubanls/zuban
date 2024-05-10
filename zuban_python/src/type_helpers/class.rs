use std::{
    borrow::Cow,
    cell::{Cell, OnceCell},
    fmt,
    rc::Rc,
};

use parsa_python_cst::{
    Argument, Arguments as CSTArguments, AssignmentContent, AsyncStmtContent, BlockContent,
    ClassDef, Decoratee, ExpressionContent, ExpressionPart, PrimaryContent, SimpleStmtContent,
    SimpleStmts, StmtContent, StmtOrError, Target, TypeLike,
};

use super::{overload::OverloadResult, Callable, Instance, LookupDetails, Module};
use crate::{
    arguments::{Args, KnownArgs, SimpleArgs},
    database::{
        BaseClass, ClassInfos, ClassKind, ClassStorage, ComplexPoint, Database, Locality,
        MetaclassState, ParentScope, Point, PointKind, PointLink, ProtocolMember,
        TypedDictDefinition,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        use_cached_annotation_type, CalculatedBaseClass, File, PythonFile, TypeComputation,
        TypeComputationOrigin, TypeVarCallbackReturn, TypeVarFinder,
    },
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{AttributeKind, FunctionOrOverload, Inferred, MroIndex},
    matching::{
        calculate_callable_init_type_vars_and_return, calculate_callable_type_vars_and_return,
        calculate_class_init_type_vars_and_return, maybe_class_usage, FormatData,
        FunctionOrCallable, Generics, LookupKind, LookupResult, Match, Matcher, MismatchReason,
        OnTypeError, ResultContext,
    },
    node_ref::NodeRef,
    python_state::NAME_TO_FUNCTION_DIFF,
    type_::{
        check_dataclass_options, dataclass_init_func, execute_functional_enum,
        infer_typed_dict_total_argument, infer_value_on_member, AnyCause, CallableContent,
        CallableLike, CallableParam, CallableParams, ClassGenerics, Dataclass, DataclassOptions,
        DbString, Enum, EnumMemberDefinition, FormatStyle, FunctionKind, FunctionOverload,
        GenericClass, GenericsList, NamedTuple, ParamType, StringSlice, Tuple, TupleArgs, Type,
        TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypedDict, TypedDictMember,
        TypedDictMemberGatherer, Variance,
    },
};

const EXCLUDED_PROTOCOL_ATTRIBUTES: [&'static str; 11] = [
    "__abstractmethods__",
    "__annotations__",
    "__dict__",
    "__doc__",
    "__init__",
    "__module__",
    "__new__",
    "__slots__",
    "__subclasshook__",
    "__weakref__",
    "__class_getitem__",
];

#[derive(Clone, Copy)]
pub struct Class<'a> {
    pub node_ref: NodeRef<'a>,
    pub class_storage: &'a ClassStorage,
    pub generics: Generics<'a>,
    pub type_var_remap: Option<&'a GenericsList>,
}

impl<'db: 'a, 'a> Class<'a> {
    pub fn new(
        node_ref: NodeRef<'a>,
        class_storage: &'a ClassStorage,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        Self {
            node_ref,
            class_storage,
            generics,
            type_var_remap,
        }
    }

    pub fn from_generic_class_components(
        db: &'db Database,
        link: PointLink,
        list: &'a ClassGenerics,
    ) -> Self {
        let generics = Generics::from_class_generics(db, list);
        Self::from_position(NodeRef::from_link(db, link), generics, None)
    }

    pub fn from_non_generic_link(db: &'db Database, link: PointLink) -> Self {
        Self::from_non_generic_node_ref(NodeRef::from_link(db, link))
    }

    pub fn from_non_generic_node_ref(node_ref: NodeRef<'db>) -> Self {
        Self::from_position(node_ref, Generics::None, None)
    }

    #[inline]
    pub fn from_position(
        node_ref: NodeRef<'a>,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        Self::new(
            node_ref,
            node_ref.expect_class_storage(),
            generics,
            type_var_remap,
        )
    }

    #[inline]
    pub fn with_undefined_generics(node_ref: NodeRef<'a>) -> Self {
        Self::from_position(node_ref, Generics::NotDefinedYet, None)
    }

    pub fn with_self_generics(db: &'a Database, node_ref: NodeRef<'a>) -> Self {
        Self::from_position(
            node_ref,
            Generics::Self_ {
                class_definition: node_ref.as_link(),
                type_var_likes: Self::with_undefined_generics(node_ref).use_cached_type_vars(db),
            },
            None,
        )
    }

    pub fn instance(self) -> Instance<'a> {
        Instance::new(self, None)
    }

    fn type_check_init_func(
        &self,
        i_s: &InferenceState<'db, '_>,
        __init__: LookupResult,
        init_class: Option<Class>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool, // Errors are different for Cls() vs. Type[Cls] that is instantiated
    ) -> Option<ClassGenerics> {
        let Some(inf) = __init__.into_maybe_inferred() else {
            if self.is_protocol(i_s.db) {
                if !from_type_type {
                    args.add_issue(i_s, IssueKind::CannotInstantiateProtocol {
                        name: self.name().into()
                    })
                }
            } else {
                debug_assert!(self.incomplete_mro(i_s.db));
            }
            let type_var_likes = self.type_vars(i_s);
            return Some(match type_var_likes.is_empty() {
                false => ClassGenerics::List(type_var_likes.as_any_generic_list()),
                true => ClassGenerics::None,
            })
        };
        match inf.init_as_function(i_s, init_class) {
            Some(FunctionOrOverload::Function(func)) => {
                let calculated_type_args = calculate_class_init_type_vars_and_return(
                    i_s,
                    self,
                    func,
                    args.iter(),
                    |issue| args.add_issue(i_s, issue),
                    result_context,
                    Some(on_type_error),
                );
                Some(calculated_type_args.type_arguments_into_class_generics())
            }
            Some(FunctionOrOverload::Callable(callable_content)) => {
                let calculated_type_args = match init_class {
                    Some(class) => todo!() /*calculate_callable_init_type_vars_and_return(
                        i_s,
                        &class,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(),
                        &|| args.as_node_ref(),
                        result_context,
                        Some(on_type_error),
                    )*/,
                    // Happens for example when NamedTuples are involved.
                    None => calculate_callable_type_vars_and_return(
                        i_s,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(),
                        |issue| args.add_issue(i_s, issue),
                        false,
                        result_context,
                        Some(on_type_error),
                    ),
                };
                Some(calculated_type_args.type_arguments_into_class_generics())
            }
            Some(FunctionOrOverload::Overload(overloaded_function)) => match overloaded_function
                .find_matching_function(
                    i_s,
                    args,
                    false,
                    Some(self),
                    true,
                    result_context,
                    on_type_error,
                ) {
                OverloadResult::Single(callable) => {
                    // Execute the found function to create the diagnostics.
                    let result = calculate_callable_init_type_vars_and_return(
                        i_s,
                        self,
                        callable,
                        args.iter(),
                        |issue| args.add_issue(i_s, issue),
                        result_context,
                        Some(on_type_error),
                    );
                    Some(result.type_arguments_into_class_generics())
                }
                OverloadResult::Union(t) => todo!(),
                OverloadResult::NotFound => None,
            },
            None => unreachable!("Should never happen, because there's always object.__init__"),
        }
    }

    pub fn node(&self) -> ClassDef<'a> {
        ClassDef::by_index(&self.node_ref.file.tree, self.node_ref.node_index)
    }

    pub fn name_string_slice(&self) -> StringSlice {
        let name = self.node().name();
        StringSlice::new(self.node_ref.file_index(), name.start(), name.end())
    }

    pub fn use_cached_type_vars(&self, db: &'db Database) -> &'a TypeVarLikes {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        debug_assert!(point.calculated());
        Self::get_calculated_type_vars(db, node_ref, point)
    }

    fn get_calculated_type_vars(
        db: &'db Database,
        node_ref: NodeRef<'a>,
        point: Point,
    ) -> &'a TypeVarLikes {
        if point.kind() == PointKind::NodeAnalysis {
            &db.python_state.empty_type_var_likes
        } else {
            match node_ref.complex().unwrap() {
                ComplexPoint::TypeVarLikes(type_vars) => type_vars,
                _ => unreachable!(),
            }
        }
    }

    pub fn type_vars(&self, i_s: &InferenceState<'db, '_>) -> &'a TypeVarLikes {
        let node_ref = self.type_vars_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return Self::get_calculated_type_vars(i_s.db, node_ref, point);
        }

        let type_vars = TypeVarFinder::find_class_type_vars(i_s, self);
        if type_vars.is_empty() {
            self.type_vars_node_ref()
                .set_point(Point::new_node_analysis(Locality::Todo));
        } else {
            self.type_vars_node_ref()
                .insert_complex(ComplexPoint::TypeVarLikes(type_vars), Locality::Todo);
        }
        self.type_vars(i_s)
    }

    pub fn maybe_type_var_like_in_parent(
        &self,
        i_s: &InferenceState<'db, '_>,
        type_var: &TypeVarLike,
    ) -> Option<TypeVarLikeUsage> {
        match self.class_storage.parent_scope {
            ParentScope::Module => None,
            ParentScope::Class(node_index) => {
                let parent_class =
                    Self::with_undefined_generics(NodeRef::new(self.node_ref.file, node_index));
                parent_class
                    .maybe_type_var_like_in_parent(i_s, type_var)
                    .or_else(|| {
                        parent_class
                            .type_vars(i_s)
                            .find(type_var.clone(), parent_class.node_ref.as_link())
                    })
            }
            ParentScope::Function(node_index) => todo!(),
        }
    }

    pub fn is_calculating_class_infos(&self) -> bool {
        self.class_info_node_ref().point().calculating()
    }

    #[inline]
    fn type_vars_node_ref(&self) -> NodeRef<'a> {
        self.node_ref.add_to_node_index(1)
    }

    #[inline]
    fn class_info_node_ref(&self) -> NodeRef<'a> {
        self.node_ref.add_to_node_index(4)
    }

    pub fn ensure_calculated_class_infos(&self, i_s: &InferenceState<'db, '_>, name_def: NodeRef) {
        let node_ref = self.class_info_node_ref();
        let point = node_ref.point();
        if point.calculated() {
            return;
        }

        debug_assert!(!name_def.point().calculated());
        debug!("Calculate class infos for {}", self.name());

        node_ref.set_point(Point::new_calculating());
        // TODO it is questionable that we are just marking this as OK, because it could be an
        // Enum / dataclass.
        name_def.set_point(Point::new_redirect(
            self.node_ref.file_index(),
            self.node_ref.node_index,
            Locality::Todo,
        ));

        let type_vars = self.type_vars(i_s);

        let mut was_dataclass = None;
        let maybe_decorated = self.node().maybe_decorated();
        let mut is_final = false;
        if let Some(decorated) = maybe_decorated {
            let inference = self.node_ref.file.inference(i_s);

            let mut dataclass_options = None;
            let dataclass_link = i_s.db.python_state.dataclasses_dataclass();
            for decorator in decorated.decorators().iter() {
                let expr = decorator.named_expression().expression();
                if let ExpressionContent::ExpressionPart(ExpressionPart::Primary(primary)) =
                    expr.unpack()
                {
                    if inference
                        .infer_primary_or_atom(primary.first())
                        .maybe_saved_link()
                        == Some(dataclass_link)
                    {
                        if let PrimaryContent::Execution(exec) = primary.second() {
                            let args =
                                SimpleArgs::new(*i_s, self.node_ref.file, primary.index(), exec);
                            dataclass_options = Some(check_dataclass_options(i_s, &args));
                            continue;
                        }
                    }
                }
                let inf = inference.infer_expression(expr);
                if let Some(maybe_link) = inf.maybe_saved_link() {
                    if maybe_link == i_s.db.python_state.typing_final().as_link() {
                        is_final = true;
                    }
                }

                if inf.maybe_saved_link() == Some(dataclass_link) {
                    dataclass_options = Some(DataclassOptions::default());
                }
            }
            if let Some(dataclass_options) = dataclass_options {
                let dataclass = Dataclass::new(
                    GenericClass {
                        link: self.node_ref.as_link(),
                        generics: if type_vars.is_empty() {
                            ClassGenerics::None
                        } else {
                            ClassGenerics::NotDefinedYet
                        },
                    },
                    dataclass_options,
                );
                was_dataclass = Some(dataclass.clone());
                let class = dataclass.class(i_s.db);
                if dataclass.options.slots && class.lookup_symbol(i_s, "__slots__").is_some() {
                    class.node_ref.add_issue(
                        i_s,
                        IssueKind::DataclassPlusExplicitSlots {
                            class_name: class.name().into(),
                        },
                    )
                }
                let new_t = Type::Type(Rc::new(Type::Dataclass(dataclass)));
                Inferred::from_type(new_t).save_redirect(i_s, name_def.file, name_def.node_index);
            }
        }

        let (mut class_infos, typed_dict_total) = self.calculate_class_infos(i_s, type_vars);
        class_infos.is_final |= is_final;
        let mut was_enum = None;
        let mut was_enum_base = false;
        if let MetaclassState::Some(link) = class_infos.metaclass {
            if link == i_s.db.python_state.enum_meta_link() {
                was_enum_base = true;
                if !self.use_cached_type_vars(i_s.db).is_empty() {
                    self.node_ref.add_issue(i_s, IssueKind::EnumCannotBeGeneric);
                }
                class_infos.class_kind = ClassKind::Enum;
                let members = self.enum_members(i_s);
                if !members.is_empty() {
                    let enum_ = Enum::new(
                        DbString::StringSlice(self.name_string_slice()),
                        self.node_ref.as_link(),
                        self.node_ref.as_link(),
                        self.class_storage.parent_scope,
                        members,
                        OnceCell::new(),
                    );
                    was_enum = Some(enum_);
                }
            }
        }
        node_ref.insert_complex(ComplexPoint::ClassInfos(class_infos), Locality::Todo);
        debug_assert!(node_ref.point().calculated());

        if let Some(decorated) = maybe_decorated {
            // TODO we pretty much just ignore the fact that a decorated class can also be an enum.
            let mut inferred = Inferred::from_saved_node_ref(self.node_ref);
            for decorator in decorated.decorators().iter_reverse() {
                if matches!(
                    decorator.as_code(),
                    "@type_check_only\n" | "@runtime_checkable\n"
                ) {
                    // TODO this branch should not be here!
                    continue;
                }
                let decorate = self
                    .node_ref
                    .file
                    .inference(i_s)
                    .infer_named_expression(decorator.named_expression());
                inferred = decorate.execute(
                    i_s,
                    &KnownArgs::new(
                        &inferred,
                        NodeRef::new(self.node_ref.file, decorator.index()),
                    ),
                );
            }
            // TODO for now don't save classdecorators, becaues they are really not used in mypy.
            // let saved = inferred.save_redirect(i_s, name_def.file, name_def.node_index);
        }

        if let Some(dataclass) = was_dataclass {
            dataclass_init_func(&dataclass, i_s.db);
        }

        if let Some(total) = typed_dict_total {
            self.insert_typed_dict_definition(i_s, name_def, total, is_final)
        };

        if let Some(enum_) = was_enum {
            let c = ComplexPoint::TypeInstance(Type::Type(Rc::new(Type::Enum(enum_.clone()))));
            // The locality is implicit, because we have a OnceCell that is inferred
            // after what we are doing here.
            name_def.insert_complex(c, Locality::ImplicitExtern);

            // Precalculate the enum values here. Note that this is intentionally done after
            // the insertion, to avoid recursions.
            // We need to calculate here, because otherwise the normal class
            // calculation will do it for us, which we probably do not want.
            for member in enum_.members.iter() {
                if member.value.is_some() {
                    infer_value_on_member(i_s, &enum_, member.value);
                }
            }
        }

        if was_enum_base {
            // Check if __new__ was correctly used in combination with enums (1)
            // Also check if mixins appear after enums (2)
            let mut had_new = 0;
            let mut enum_spotted: Option<Class> = None;
            for base in self.bases(i_s.db) {
                if let TypeOrClass::Class(c) = &base {
                    let is_enum = c.use_cached_class_infos(i_s.db).class_kind == ClassKind::Enum;
                    let has_mixin_enum_new = if is_enum {
                        c.bases(i_s.db).any(|inner| match inner {
                            TypeOrClass::Class(inner) => {
                                inner.use_cached_class_infos(i_s.db).class_kind != ClassKind::Enum
                                    && inner.has_customized_enum_new(i_s)
                            }
                            TypeOrClass::Type(_) => false,
                        })
                    } else {
                        c.has_customized_enum_new(i_s)
                    };
                    // (1)
                    if has_mixin_enum_new {
                        had_new += 1;
                        if had_new > 1 {
                            self.node_ref.add_issue(
                                i_s,
                                IssueKind::EnumMultipleMixinNew {
                                    extra: c.format(&FormatData::with_style(
                                        i_s.db,
                                        FormatStyle::Qualified,
                                    )),
                                },
                            );
                        }
                    }
                    // (2)
                    match enum_spotted {
                        Some(after) if !is_enum => {
                            self.node_ref.add_issue(
                                i_s,
                                IssueKind::EnumMixinNotAllowedAfterEnum {
                                    after: after.format(&FormatData::with_style(
                                        i_s.db,
                                        FormatStyle::Qualified,
                                    )),
                                },
                            );
                        }
                        _ => {
                            if is_enum {
                                enum_spotted = Some(*c);
                            }
                        }
                    }
                }
            }
        }
        debug!("Finished calculating class infos for {}", self.name());
    }

    pub fn use_cached_class_infos(&self, db: &'db Database) -> &'db ClassInfos {
        self.maybe_cached_class_infos(db).unwrap()
    }

    pub fn incomplete_mro(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).incomplete_mro
    }

    pub fn maybe_cached_class_infos(&self, db: &'db Database) -> Option<&'db ClassInfos> {
        let node_ref = self.class_info_node_ref();
        if !node_ref.point().calculated() {
            return None;
        }
        match node_ref.to_db_lifetime(db).complex().unwrap() {
            ComplexPoint::ClassInfos(class_infos) => Some(class_infos),
            _ => unreachable!(),
        }
    }

    pub fn bases(&self, db: &'a Database) -> impl Iterator<Item = TypeOrClass<'a>> {
        let generics = self.generics;
        self.use_cached_class_infos(db)
            .mro
            .iter()
            .filter_map(move |b| {
                b.is_direct_base
                    .then(|| apply_generics_to_base_class(db, &b.type_, generics))
            })
    }

    fn calculate_class_infos(
        &self,
        i_s: &InferenceState<'db, '_>,
        type_vars: &TypeVarLikes,
    ) -> (Box<ClassInfos>, Option<bool>) {
        // Calculate all type vars beforehand
        let db = i_s.db;

        let mut bases: Vec<Type> = vec![];
        let mut incomplete_mro = false;
        let mut class_kind = ClassKind::Normal;
        let mut typed_dict_total = None;
        let mut had_new_typed_dict = false;
        let mut is_new_named_tuple = false;
        let mut metaclass = MetaclassState::None;
        let mut has_slots = self.class_storage.slots.is_some();
        let mut is_final = false;
        let arguments = self.node().arguments();
        if let Some(arguments) = arguments {
            // Check metaclass before checking all the arguments, because it has a preference over
            // the metaclasses of the subclasses.
            for argument in arguments.iter() {
                if let Argument::Keyword(kwarg) = argument {
                    let (name, expr) = kwarg.unpack();
                    if name.as_str() == "metaclass" {
                        let node_ref = NodeRef::new(self.node_ref.file, expr.index());
                        let mut inference = self.node_ref.file.inference(i_s);
                        let meta_base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                todo!();
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(expr);
                        match meta_base {
                            CalculatedBaseClass::Type(Type::Class(GenericClass {
                                link,
                                generics: ClassGenerics::None,
                            })) => {
                                let c = Class::from_non_generic_link(db, link);
                                if c.incomplete_mro(db)
                                    || c.class_link_in_mro(
                                        db,
                                        db.python_state.bare_type_node_ref().as_link(),
                                    )
                                {
                                    Self::update_metaclass(
                                        i_s,
                                        node_ref,
                                        &mut metaclass,
                                        MetaclassState::Some(link),
                                    )
                                } else {
                                    node_ref
                                        .add_issue(i_s, IssueKind::MetaclassMustInheritFromType);
                                }
                            }
                            CalculatedBaseClass::Unknown => {
                                if i_s.db.project.flags.disallow_subclassing_any {
                                    NodeRef::new(self.node_ref.file, kwarg.index()).add_issue(
                                        i_s,
                                        IssueKind::DisallowedAnyMetaclass {
                                            class: expr.as_code().into(),
                                        },
                                    );
                                }
                                metaclass = MetaclassState::Unknown
                            }
                            _ => {
                                node_ref.add_issue(i_s, IssueKind::InvalidMetaclass);
                            }
                        }
                    }
                }
            }

            // Calculate the type var remapping
            for argument in arguments.iter() {
                match argument {
                    Argument::Positional(n) => {
                        let mut inference = self.node_ref.file.inference(i_s);
                        let base = TypeComputation::new(
                            &mut inference,
                            self.node_ref.as_link(),
                            &mut |i_s, _: &_, type_var_like: TypeVarLike, _| {
                                if let Some(usage) =
                                    type_vars.find(type_var_like.clone(), self.node_ref.as_link())
                                {
                                    return TypeVarCallbackReturn::TypeVarLike(usage);
                                } else if let Some(usage) =
                                    self.maybe_type_var_like_in_parent(i_s, &type_var_like)
                                {
                                    TypeVarCallbackReturn::TypeVarLike(usage)
                                } else {
                                    // This can happen if two type var likes are used.
                                    TypeVarCallbackReturn::NotFound
                                }
                            },
                            TypeComputationOrigin::BaseClass,
                        )
                        .compute_base_class(n.expression());
                        match base {
                            CalculatedBaseClass::Type(t) => {
                                if let Some(name) = bases
                                    .iter()
                                    .find_map(|base| base.check_duplicate_base_class(db, &t))
                                {
                                    NodeRef::new(self.node_ref.file, n.index())
                                        .add_issue(i_s, IssueKind::DuplicateBaseClass { name });
                                    incomplete_mro = true;
                                    continue;
                                }
                                bases.push(t);
                                let class = match &bases.last().unwrap() {
                                    Type::Class(c) => {
                                        if let Some(cached) =
                                            c.class(i_s.db).maybe_cached_class_infos(i_s.db)
                                        {
                                            if cached.class_kind != ClassKind::Normal {
                                                if class_kind == ClassKind::Normal {
                                                    if !matches!(
                                                        cached.class_kind,
                                                        ClassKind::Protocol
                                                    ) {
                                                        class_kind = cached.class_kind.clone();
                                                    }
                                                }
                                            }
                                        }
                                        Some(c.class(db))
                                    }
                                    Type::Tuple(content) => {
                                        if class_kind == ClassKind::Normal {
                                            class_kind = ClassKind::Tuple;
                                        } else {
                                            todo!()
                                        }
                                        None
                                    }
                                    Type::Dataclass(d) => Some(d.class(db)),
                                    Type::TypedDict(typed_dict) => {
                                        if typed_dict_total.is_none() {
                                            typed_dict_total =
                                                Some(self.check_total_typed_dict_argument(
                                                    i_s, arguments,
                                                ))
                                        }
                                        class_kind = ClassKind::TypedDict;
                                        if typed_dict.is_final {
                                            NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                                i_s,
                                                IssueKind::CannotInheritFromFinalClass {
                                                    class_name: Box::from(
                                                        typed_dict.name.unwrap().as_str(i_s.db),
                                                    ),
                                                },
                                            );
                                        }
                                        continue;
                                    }
                                    _ => unreachable!(),
                                };
                                if let Some(class) = class {
                                    if class.is_calculating_class_infos() {
                                        let name = Box::<str>::from(class.name());
                                        bases.pop();
                                        incomplete_mro = true;
                                        NodeRef::new(self.node_ref.file, n.index())
                                            .add_issue(i_s, IssueKind::CyclicDefinition { name });
                                    } else {
                                        let cached_class_infos = class.use_cached_class_infos(db);
                                        if cached_class_infos.is_final {
                                            is_final = cached_class_infos.is_final;
                                            NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                                i_s,
                                                IssueKind::CannotInheritFromFinalClass {
                                                    class_name: Box::from(class.name()),
                                                },
                                            );
                                        }
                                        incomplete_mro |= cached_class_infos.incomplete_mro;
                                        has_slots |= cached_class_infos.has_slots;
                                        Self::update_metaclass(
                                            i_s,
                                            NodeRef::new(self.node_ref.file, n.index()),
                                            &mut metaclass,
                                            cached_class_infos.metaclass,
                                        );
                                        match &cached_class_infos.class_kind {
                                            ClassKind::NamedTuple => {
                                                if matches!(
                                                    class_kind,
                                                    ClassKind::Normal | ClassKind::NamedTuple
                                                ) {
                                                    class_kind = ClassKind::NamedTuple;
                                                } else {
                                                    todo!()
                                                }
                                            }
                                            ClassKind::TypedDict => unreachable!(),
                                            _ => (),
                                        }
                                    }
                                }
                            }
                            // TODO this might overwrite other class types
                            CalculatedBaseClass::Protocol => {
                                class_kind = ClassKind::Protocol;
                                metaclass = MetaclassState::Some(db.python_state.abc_meta_link())
                            }
                            CalculatedBaseClass::NamedTuple(named_tuple) => {
                                let named_tuple =
                                    named_tuple.clone_with_new_init_class(self.name_string_slice());
                                bases.push(Type::NamedTuple(named_tuple));
                                class_kind = ClassKind::NamedTuple;
                            }
                            CalculatedBaseClass::NewNamedTuple => {
                                is_new_named_tuple = true;
                                let named_tuple = self
                                    .named_tuple_from_class(&i_s.with_class_context(self), *self);
                                bases.push(Type::NamedTuple(named_tuple));
                                class_kind = ClassKind::NamedTuple;
                            }
                            CalculatedBaseClass::TypedDict => {
                                if had_new_typed_dict {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::DuplicateBaseClass {
                                            name: "TypedDict".into(),
                                        },
                                    );
                                } else {
                                    had_new_typed_dict = true;
                                    class_kind = ClassKind::TypedDict;
                                    if typed_dict_total.is_none() {
                                        typed_dict_total = Some(
                                            self.check_total_typed_dict_argument(i_s, arguments),
                                        )
                                    }
                                }
                            }
                            CalculatedBaseClass::Generic => (),
                            CalculatedBaseClass::Unknown => {
                                if i_s.db.project.flags.disallow_subclassing_any {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::DisallowedAnySubclass {
                                            class: n.as_code().into(),
                                        },
                                    );
                                }
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::InvalidEnum(enum_) => {
                                let name = enum_.name.as_str(i_s.db);
                                NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                    i_s,
                                    IssueKind::EnumWithMembersNotExtendable { name: name.into() },
                                );
                                if enum_.class(i_s.db).use_cached_class_infos(i_s.db).is_final {
                                    NodeRef::new(self.node_ref.file, n.index()).add_issue(
                                        i_s,
                                        IssueKind::CannotInheritFromFinalClass {
                                            class_name: Box::from(name),
                                        },
                                    );
                                }
                                incomplete_mro = true;
                            }
                            CalculatedBaseClass::Invalid => {
                                NodeRef::new(self.node_ref.file, n.index())
                                    .add_issue(i_s, IssueKind::InvalidBaseClass);
                                incomplete_mro = true;
                            }
                        };
                    }
                    Argument::Keyword(kwarg) => {
                        let (name, expr) = kwarg.unpack();
                        if name.as_str() != "metaclass" {
                            // Generate diagnostics
                            self.node_ref.file.inference(i_s).infer_expression(expr);
                            debug!("TODO shouldn't we handle this? In testNewAnalyzerClassKeywordsForward it's ignored...")
                        }
                    }
                    Argument::Star(starred) => {
                        NodeRef::new(self.node_ref.file, starred.index())
                            .add_issue(i_s, IssueKind::InvalidBaseClass);
                    }
                    Argument::StarStar(double_starred) => {
                        NodeRef::new(self.node_ref.file, double_starred.index())
                            .add_issue(i_s, IssueKind::InvalidBaseClass);
                    }
                }
            }
        }
        match class_kind {
            ClassKind::TypedDict => {
                if bases.iter().any(|t| !matches!(t, Type::TypedDict(_))) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_issue(i_s, IssueKind::TypedDictBasesMustBeTypedDicts);
                }
            }
            ClassKind::Protocol => {
                if bases.iter().any(|t| {
                    t.maybe_class(i_s.db).map_or(true, |cls| {
                        !cls.is_protocol(i_s.db)
                            && cls.node_ref != i_s.db.python_state.object_node_ref()
                    })
                }) {
                    NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                        .add_issue(i_s, IssueKind::BasesOfProtocolMustBeProtocol);
                }
            }
            _ => (),
        }
        if is_new_named_tuple && bases.len() > 1 {
            NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                .add_issue(i_s, IssueKind::NamedTupleShouldBeASingleBase);
        }

        let mro = linearize_mro(i_s, self, &bases);

        let mut found_tuple_like = None;
        for base in mro.iter() {
            if matches!(base.type_, Type::Tuple(_) | Type::NamedTuple(_)) {
                if let Some(found_tuple_like) = found_tuple_like {
                    if found_tuple_like != &base.type_ {
                        NodeRef::new(self.node_ref.file, arguments.unwrap().index())
                            .add_issue(i_s, IssueKind::IncompatibleBaseTuples);
                    }
                } else {
                    found_tuple_like = Some(&base.type_);
                }
            }
        }
        let protocol_members = if class_kind == ClassKind::Protocol {
            self.gather_protocol_members()
        } else {
            Default::default()
        };
        (
            Box::new(ClassInfos {
                mro,
                metaclass,
                incomplete_mro,
                class_kind,
                has_slots,
                protocol_members,
                is_final,
            }),
            typed_dict_total,
        )
    }

    fn update_metaclass(
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        current: &mut MetaclassState,
        new: MetaclassState,
    ) {
        match new {
            MetaclassState::None => (),
            MetaclassState::Unknown => {
                if *current == MetaclassState::None {
                    *current = MetaclassState::Unknown
                }
            }
            MetaclassState::Some(link2) => match current {
                MetaclassState::Some(link1) => {
                    let t1 = Type::Class(GenericClass {
                        link: *link1,
                        generics: ClassGenerics::None,
                    });
                    let t2 = Type::Class(GenericClass {
                        link: link2,
                        generics: ClassGenerics::None,
                    });
                    if !t1.is_simple_sub_type_of(i_s, &t2).bool() {
                        if t2.is_simple_sub_type_of(i_s, &t1).bool() {
                            *current = new
                        } else {
                            node_ref.add_issue(i_s, IssueKind::MetaclassConflict);
                        }
                    }
                }
                _ => *current = new,
            },
        }
    }

    fn check_total_typed_dict_argument(&self, i_s: &InferenceState, args: CSTArguments) -> bool {
        let mut total = true;
        let inference = self.node_ref.file.inference(i_s);
        for argument in args.iter() {
            if let Argument::Keyword(kwarg) = argument {
                let (name, expr) = kwarg.unpack();
                if name.as_code() == "total" {
                    let inf = inference.infer_expression(expr);
                    total = infer_typed_dict_total_argument(i_s, inf, |issue| {
                        NodeRef::new(self.node_ref.file, expr.index()).add_issue(i_s, issue)
                    })
                    .unwrap_or(true);
                }
            }
        }
        total
    }

    pub fn is_metaclass(&self, db: &Database) -> bool {
        let python_type = db.python_state.bare_type_type();
        self.use_cached_class_infos(db)
            .mro
            .iter()
            .any(|t| t.type_ == python_type)
    }

    pub fn maybe_metaclass(&self, db: &Database) -> Option<PointLink> {
        match self.use_cached_class_infos(db).metaclass {
            MetaclassState::Some(link) => Some(link),
            _ => None,
        }
    }

    pub fn is_base_exception_group(&self, db: &Database) -> bool {
        db.python_state
            .base_exception_group_node_ref()
            .is_some_and(|g| self.class_link_in_mro(db, g.as_link()))
    }

    pub fn is_base_exception(&self, db: &Database) -> bool {
        self.class_link_in_mro(db, db.python_state.base_exception_node_ref().as_link())
    }

    pub fn is_exception(&self, db: &Database) -> bool {
        self.class_link_in_mro(db, db.python_state.exception_node_ref().as_link())
    }

    pub fn is_protocol(&self, db: &Database) -> bool {
        self.use_cached_class_infos(db).class_kind == ClassKind::Protocol
    }

    pub fn check_protocol_match(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        other: &Type,
    ) -> Match {
        const SHOW_MAX_MISMATCHES: usize = 2;
        const MAX_MISSING_MEMBERS: usize = 2;
        let mut missing_members = vec![];
        let mut mismatches = 0;
        let mut notes = vec![];
        let mut had_conflict_note = false;
        let mut had_at_least_one_member_with_same_name = false;

        let ignore_positional_param_names_old = matcher.ignore_positional_param_names;
        matcher.ignore_positional_param_names = true;

        debug!(
            r#"Match protocol "{}" against "{}""#,
            self.format_short(i_s.db),
            other.format_short(i_s.db)
        );
        let mut protocol_member_count = 0;
        debug!("TODO this from is completely wrong and should never be used.");
        for (mro_index, c) in self.mro_maybe_without_object(i_s.db, true) {
            let TypeOrClass::Class(c) = c else {
                todo!()
            };
            let protocol_members = &c.use_cached_class_infos(i_s.db).protocol_members;
            protocol_member_count += protocol_members.len();
            for protocol_member in protocol_members.iter() {
                let name = NodeRef::new(c.node_ref.file, protocol_member.name_index).as_code();
                // It is possible to match a Callable against a Protocol that only implements
                // __call__.
                let is_call = name == "__call__";
                let mut mismatch = false;
                if is_call {
                    // __call__ matching doesn't ignore param names, matching all other methods
                    // does.
                    matcher.ignore_positional_param_names = false;
                    if !matches!(other, Type::Class(_)) {
                        let inf1 = Instance::new(c, None)
                            .type_lookup(i_s, |issue| todo!(), name)
                            .into_inferred();
                        let t1 = inf1.as_cow_type(i_s);
                        if t1
                            .matches(i_s, matcher, other, protocol_member.variance)
                            .bool()
                        {
                            matcher.ignore_positional_param_names = true;
                            had_at_least_one_member_with_same_name = true;
                            continue;
                        }
                        mismatch = true;
                    }
                }

                let mut had_lookup_error = false;
                other.run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    self.node_ref.file_index(),
                    name,
                    LookupKind::Normal,
                    &mut ResultContext::Unknown,
                    &|issue| todo!(),
                    &mut |_, lookup_details| {
                        if matches!(lookup_details.lookup, LookupResult::None) {
                            had_lookup_error = true;
                        } else {
                            had_at_least_one_member_with_same_name = true;
                            let protocol_lookup_details = Instance::new(c, None).lookup_with_details(
                                i_s,
                                |issue| todo!(),
                                name,
                                LookupKind::Normal,
                            );
                            let inf1 = protocol_lookup_details.lookup.into_inferred();
                            let t1 = inf1.as_cow_type(i_s);
                            let lookup = lookup_details.lookup.into_inferred();
                            let t2 = lookup.as_cow_type(i_s);
                            let m = t1.matches(i_s, matcher, &t2, protocol_member.variance);
                            if m.bool() && !(is_call && !matches!(other, Type::Class(_))) {
                            } else {
                                if !had_conflict_note {
                                    had_conflict_note = true;
                                    notes.push(protocol_conflict_note(i_s.db, other));
                                }
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    match other.maybe_class(i_s.db) {
                                        Some(cls) => add_protocol_mismatch(
                                            i_s,
                                            &mut notes,
                                            name,
                                            &t1,
                                            &t2,
                                            &c.lookup(i_s, |_| (), name, LookupKind::Normal)
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                            &cls.lookup(i_s, |_| (), name, LookupKind::Normal)
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                        ),
                                        None => {
                                            let full_other = match other {
                                                Type::Type(t) if is_call => {
                                                    t.maybe_class(i_s.db).and_then(|cls| {
                                                        notes.push(format!(r#""{}" has constructor incompatible with "__call__" of "{}""#, cls.name(), self.name()).into());
                                                        cls.find_relevant_constructor(i_s).as_type(i_s, cls)
                                                    })
                                                }
                                                _ => None,
                                            };
                                            add_protocol_mismatch(
                                                i_s,
                                                &mut notes,
                                                name,
                                                &t1,
                                                &t2,
                                                &t1,
                                                &full_other.as_ref().unwrap_or(&t2),
                                            )
                                        }
                                    }
                                }
                            }
                            if lookup_details.attr_kind.is_read_only_property()
                                && !protocol_lookup_details.attr_kind.is_read_only_property()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(format!("Protocol member {}.{name} expected settable variable, got read-only attribute", self.name()).into());
                                }
                            }
                            if matches!(protocol_lookup_details.attr_kind, AttributeKind::ClassVar)
                                && !matches!(lookup_details.attr_kind, AttributeKind::ClassVar)
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(format!("Protocol member {}.{name} expected class variable, got instance variable", self.name()).into());
                                }
                            }
                            if protocol_lookup_details.attr_kind.classmethod_or_staticmethod()
                                && !lookup_details.attr_kind.classmethod_or_staticmethod()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(format!("Protocol member {}.{name} expected class or static method", self.name()).into());
                                }
                            }
                            if lookup_details.attr_kind == AttributeKind::AnnotatedAttribute {
                                if let Type::Type(t) = other {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(format!(
                                            "Only class variables allowed for class object access \
                                             on protocols, {} is an instance variable of \"{}\"",
                                            name,
                                            t.format_short(i_s.db),
                                        ).into());
                                    }
                                }
                            }
                        }
                    }
                );
                if had_lookup_error {
                    missing_members.push(name);
                }
                if is_call {
                    matcher.ignore_positional_param_names = true;
                }
                mismatches += mismatch as usize;
            }
        }
        if !had_at_least_one_member_with_same_name && !missing_members.is_empty() {
            return Match::new_false();
        }
        if mismatches > SHOW_MAX_MISMATCHES {
            notes.push(
                format!(
                    "    <{} more conflict(s) not shown>",
                    mismatches - SHOW_MAX_MISMATCHES
                )
                .into(),
            );
        }
        let missing_members_empty = missing_members.is_empty();
        if !missing_members_empty
            && protocol_member_count > 1
            && missing_members.len() <= MAX_MISSING_MEMBERS
        {
            let tmp;
            notes.push(
                format!(
                    r#""{}" is missing following "{}" protocol member:"#,
                    match other.maybe_class(i_s.db) {
                        Some(cls) => cls.name(),
                        None => {
                            tmp = other.format_short(i_s.db);
                            tmp.as_ref()
                        }
                    },
                    self.name()
                )
                .into(),
            );
            for name in missing_members {
                notes.push(format!("    {name}").into());
            }
        }
        matcher.ignore_positional_param_names = ignore_positional_param_names_old;
        if notes.is_empty() && missing_members_empty {
            Match::new_true()
        } else {
            Match::False {
                similar: false,
                reason: MismatchReason::ProtocolMismatches {
                    notes: notes.into_boxed_slice(),
                },
            }
        }
    }

    pub fn has_customized_enum_new(&self, i_s: &InferenceState) -> bool {
        for (_, c) in self.mro_maybe_without_object(i_s.db, true) {
            let (c, lookup) = c.lookup_symbol(i_s, "__new__");
            if lookup.into_maybe_inferred().is_some() {
                let Some(class) = c else {
                    unreachable!()
                };
                return class.node_ref.file.file_index()
                    != i_s.db.python_state.enum_file().file_index();
            }
        }
        false
    }

    pub fn lookup_symbol(&self, i_s: &InferenceState<'db, '_>, name: &str) -> LookupResult {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => LookupResult::None,
            Some(node_index) => {
                let inf = self
                    .node_ref
                    .file
                    .inference(&i_s.with_class_context(self))
                    .infer_name_of_definition_by_index(node_index);
                LookupResult::GotoName {
                    name: PointLink::new(self.node_ref.file.file_index(), node_index),
                    inf,
                }
            }
        }
    }

    fn lookup_and_class_and_maybe_ignore_self_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        ignore_self: bool,
    ) -> (LookupResult, TypeOrClass<'a>, MroIndex) {
        for (mro_index, c) in self
            .mro_maybe_without_object(i_s.db, self.incomplete_mro(i_s.db))
            .skip(ignore_self as usize)
        {
            let (_, result) = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                return match c {
                    // TODO why?
                    TypeOrClass::Type(t) if matches!(t.as_ref(), Type::NamedTuple(_)) => (
                        result,
                        TypeOrClass::Class(i_s.db.python_state.typing_named_tuple_class()),
                        mro_index,
                    ),
                    _ => (result, c, mro_index),
                };
            }
        }
        (
            LookupResult::None,
            TypeOrClass::Type(Cow::Owned(Type::Any(AnyCause::Internal))),
            0.into(),
        )
    }

    pub(crate) fn lookup_and_class_and_maybe_ignore_self(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
        ignore_self: bool,
    ) -> LookupDetails {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            add_issue,
            name,
            kind,
            false,
            ignore_self,
        )
    }

    pub fn lookup_without_descriptors(
        &self,
        i_s: &InferenceState<'db, '_>,
        node_ref: NodeRef,
        name: &str,
    ) -> LookupDetails {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            |issue| node_ref.add_issue(i_s, issue),
            name,
            LookupKind::Normal,
            false,
            false,
        )
    }

    pub(crate) fn lookup_without_descriptors_and_custom_add_issue(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        add_issue: impl Fn(IssueKind),
    ) -> LookupDetails {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            add_issue,
            name,
            LookupKind::Normal,
            false,
            false,
        )
    }

    pub(crate) fn lookup_without_descriptors_and_custom_add_issue_ignore_self(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        add_issue: impl Fn(IssueKind),
    ) -> LookupDetails {
        self.lookup_with_or_without_descriptors_internal(
            i_s,
            add_issue,
            name,
            LookupKind::Normal,
            false,
            true,
        )
    }

    pub(crate) fn lookup_with_custom_self_type(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
        as_type_type: impl Fn() -> Type,
    ) -> LookupDetails<'a> {
        self.lookup_internal_detailed(i_s, add_issue, name, kind, true, false, as_type_type)
    }

    fn lookup_with_or_without_descriptors_internal(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
        use_descriptors: bool,
        ignore_self: bool,
    ) -> LookupDetails<'a> {
        self.lookup_internal_detailed(
            i_s,
            add_issue,
            name,
            kind,
            use_descriptors,
            ignore_self,
            || self.as_type_type(i_s),
        )
    }

    fn lookup_internal_detailed(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
        use_descriptors: bool,
        ignore_self: bool,
        as_type_type: impl Fn() -> Type,
    ) -> LookupDetails<'a> {
        let class_infos = self.use_cached_class_infos(i_s.db);
        let result = if kind == LookupKind::Normal {
            if class_infos.class_kind == ClassKind::Enum && use_descriptors && name == "_ignore_" {
                return LookupDetails {
                    lookup: LookupResult::None,
                    class: TypeOrClass::Class(*self),
                    attr_kind: AttributeKind::Attribute,
                };
            }
            let (lookup_result, in_class, _) =
                self.lookup_and_class_and_maybe_ignore_self_internal(i_s, name, ignore_self);
            let mut attr_kind = AttributeKind::Attribute;
            let result = lookup_result.and_then(|inf| {
                if let TypeOrClass::Class(in_class) = in_class {
                    if class_infos.has_slots {
                        if self.in_slots(i_s.db, name) {
                            add_issue(IssueKind::SlotsConflictWithClassVariableAccess {
                                name: name.into(),
                            })
                        }
                    }
                    let i_s = i_s.with_class_context(&in_class);
                    let result = inf.bind_class_descriptors(
                        &i_s,
                        self,
                        in_class,
                        &add_issue,
                        use_descriptors,
                    );
                    if let Some((_, k)) = &result {
                        attr_kind = *k;
                    }
                    result.map(|inf| inf.0)
                } else {
                    Some(inf)
                }
            });
            result.map(|lookup| LookupDetails {
                class: in_class,
                lookup,
                attr_kind,
            })
        } else {
            None
        };
        match result {
            Some(LookupDetails {
                lookup: LookupResult::None,
                ..
            })
            | None => {
                let metaclass_result = match class_infos.metaclass {
                    MetaclassState::Unknown => LookupDetails::any(AnyCause::Todo),
                    _ => {
                        let instance = Instance::new(class_infos.metaclass(i_s.db), None);
                        instance.lookup_with_explicit_self_binding(
                            i_s,
                            &|issue| add_issue(issue),
                            name,
                            LookupKind::Normal,
                            0,
                            as_type_type,
                        )
                    }
                };
                if matches!(&metaclass_result.lookup, LookupResult::None)
                    && self.incomplete_mro(i_s.db)
                {
                    LookupDetails::any(AnyCause::Todo)
                } else {
                    LookupDetails {
                        class: TypeOrClass::Class(*self),
                        lookup: metaclass_result.lookup,
                        attr_kind: metaclass_result.attr_kind,
                    }
                }
            }
            Some(result) => result,
        }
    }

    pub fn generics(&self) -> Generics {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn has_simple_self_generics(&self) -> bool {
        matches!(self.generics, Generics::Self_ { .. }) && self.type_var_remap.is_none()
    }

    pub fn nth_type_argument(&self, db: &Database, nth: usize) -> Type {
        let type_vars = self.use_cached_type_vars(db);
        self.generics()
            .nth_type_argument(db, &type_vars[nth], nth)
            .into_owned()
    }

    fn mro_maybe_without_object(
        &self,
        db: &'db Database,
        without_object: bool,
    ) -> MroIterator<'db, 'a> {
        let class_infos = self.use_cached_class_infos(db);
        MroIterator::new(
            db,
            TypeOrClass::Class(*self),
            self.generics,
            class_infos.mro.iter(),
            without_object
                || self.node_ref == db.python_state.object_node_ref()
                || class_infos.class_kind == ClassKind::Protocol,
        )
    }

    pub fn mro(&self, db: &'db Database) -> MroIterator<'db, 'a> {
        self.mro_maybe_without_object(db, self.node_ref == db.python_state.object_node_ref())
    }

    pub fn class_link_in_mro(&self, db: &'db Database, link: PointLink) -> bool {
        if self.node_ref.as_link() == link {
            return true;
        }
        let class_infos = self.use_cached_class_infos(db);
        class_infos
            .mro
            .iter()
            .any(|b| matches!(&b.type_, Type::Class(c) if link == c.link))
    }

    pub fn is_object_class(&self, db: &Database) -> bool {
        self.node_ref == db.python_state.object_node_ref()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut result = match format_data.style {
            FormatStyle::Short => self.name().to_owned(),
            FormatStyle::Qualified | FormatStyle::MypyRevealType => {
                self.qualified_name(format_data.db)
            }
        };
        let type_var_likes = self.type_vars(&InferenceState::new(format_data.db));
        if !type_var_likes.is_empty() {
            result += &self
                .generics()
                .format(format_data, Some(type_var_likes.len()));
        }

        if let Some(class_infos) = self.maybe_cached_class_infos(format_data.db) {
            match &class_infos.class_kind {
                ClassKind::NamedTuple => {
                    let named_tuple = class_infos.maybe_named_tuple().unwrap();
                    return named_tuple.format_with_name(format_data, &result, self.generics);
                }
                ClassKind::Tuple if format_data.style == FormatStyle::MypyRevealType => {
                    for (_, type_or_class) in self.mro(format_data.db) {
                        if let TypeOrClass::Type(t) = type_or_class {
                            if let Type::Tuple(tup) = t.as_ref() {
                                if matches!(
                                    tup.args,
                                    TupleArgs::FixedLen(_) | TupleArgs::WithUnpack(_)
                                ) {
                                    return tup.format_with_fallback(
                                        format_data,
                                        &format!(", fallback={result}"),
                                    );
                                }
                            }
                        }
                    }
                }
                _ => (),
            }
        }
        result.into()
    }

    pub fn format_short(&self, db: &Database) -> Box<str> {
        self.format(&FormatData::new_short(db))
    }

    pub fn as_inferred(&self, i_s: &InferenceState) -> Inferred {
        Inferred::from_type(self.as_type_type(i_s))
    }

    pub fn generics_as_list(&self, db: &Database) -> ClassGenerics {
        // TODO we instantiate, because we cannot use use_cached_type_vars?
        let type_vars = self.type_vars(&InferenceState::new(db));
        self.generics().as_generics_list(db, type_vars)
    }

    pub fn as_generic_class(&self, db: &Database) -> GenericClass {
        GenericClass {
            link: self.node_ref.as_link(),
            generics: self.generics_as_list(db),
        }
    }

    pub fn as_type(&self, db: &Database) -> Type {
        Type::Class(self.as_generic_class(db))
    }

    pub fn as_type_type(&self, i_s: &InferenceState<'db, '_>) -> Type {
        Type::Type(Rc::new(self.as_type(i_s.db)))
    }

    fn named_tuple_from_class(&self, i_s: &InferenceState, cls: Class) -> Rc<NamedTuple> {
        let name = self.name_string_slice();
        Rc::new(NamedTuple::new(
            name,
            self.initialize_named_tuple_class_members(i_s, name),
        ))
    }

    fn initialize_named_tuple_class_members(
        &self,
        i_s: &InferenceState,
        name: StringSlice,
    ) -> CallableContent {
        let mut vec = start_namedtuple_params(i_s.db);
        let file = self.node_ref.file;
        match self.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    let StmtOrError::Stmt(stmt) = stmt else {
                        continue
                    };
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_named_tuple_types(i_s, file, &mut vec, simple)
                        }
                        StmtContent::FunctionDef(_) => (),
                        StmtContent::AsyncStmt(async_stmt)
                            if matches!(async_stmt.unpack(), AsyncStmtContent::FunctionDef(_)) => {}
                        StmtContent::Decorated(dec)
                            if matches!(
                                dec.decoratee(),
                                Decoratee::FunctionDef(_) | Decoratee::AsyncFunctionDef(_)
                            ) => {}
                        _ => NodeRef::new(file, stmt.index())
                            .add_issue(i_s, IssueKind::InvalidStmtInNamedTuple),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_named_tuple_types(i_s, file, &mut vec, simple),
        }
        let tvls = self.use_cached_type_vars(i_s.db);
        CallableContent {
            name: Some(DbString::StringSlice(name)),
            class_name: None,
            defined_at: self.node_ref.as_link(),
            kind: FunctionKind::Function {
                had_first_self_or_class_annotation: true,
            },
            type_vars: self.use_cached_type_vars(i_s.db).clone(),
            guard: None,
            is_abstract: false,
            params: CallableParams::Simple(Rc::from(vec)),
            return_type: Type::Self_,
        }
    }

    fn insert_typed_dict_definition(
        &self,
        i_s: &InferenceState,
        name_def: NodeRef,
        total: bool,
        is_final: bool,
    ) {
        let td = TypedDict::new_class_definition(
            self.name_string_slice(),
            self.node_ref.as_link(),
            self.type_vars(i_s).clone(),
            is_final,
        );
        name_def.insert_complex(
            ComplexPoint::TypedDictDefinition(TypedDictDefinition::new(td.clone(), total)),
            Locality::ImplicitExtern,
        );
        self.initialize_typed_dict_members(i_s, td);
    }

    fn initialize_typed_dict_members(&self, i_s: &InferenceState, typed_dict: Rc<TypedDict>) {
        let typed_dict_definition = self.maybe_typed_dict_definition().unwrap();
        let i_s = &i_s.with_class_context(self);
        let mut typed_dict_members = TypedDictMemberGatherer::default();
        if let Some(args) = self.node().arguments() {
            for (i, base) in self
                .use_cached_class_infos(i_s.db)
                .mro
                .iter()
                .rev()
                .filter(|t| t.is_direct_base)
                .enumerate()
            {
                match &base.type_ {
                    Type::TypedDict(td) => {
                        let node_ref =
                            NodeRef::new(self.node_ref.file, args.iter().nth(i).unwrap().index());
                        let Some(super_class_members) = td.maybe_calculated_members(i_s.db) else {
                            let super_cls = Class::from_non_generic_link(i_s.db, td.defined_at);
                            let tdd = super_cls.maybe_typed_dict_definition().unwrap();
                            tdd.deferred_subclass_member_initializations.borrow_mut().push(typed_dict.clone());
                            debug!(
                                "Defer typed dict member initialization for {:?} after {:?}",
                                self.name(),
                                super_cls.name(),
                            );
                            return
                        };
                        typed_dict_members.merge(i_s, node_ref, td.members(i_s.db));
                    }
                    _ => (),
                }
            }
        }
        debug!("Start TypedDict members calculation for {:?}", self.name());
        let file = self.node_ref.file;
        match self.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    let StmtOrError::Stmt(stmt) = stmt else {
                        continue
                    };
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => find_stmt_typed_dict_types(
                            i_s,
                            file,
                            &mut typed_dict_members,
                            simple,
                            typed_dict_definition.total,
                        ),
                        _ => NodeRef::new(file, stmt.index())
                            .add_issue(i_s, IssueKind::TypedDictInvalidMember),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_typed_dict_types(i_s, file, &mut vec, simple),
        }
        debug!("End TypedDict members calculation for {:?}", self.name());
        typed_dict.late_initialization_of_members(typed_dict_members.into_boxed_slice());
        loop {
            let mut borrowed = typed_dict_definition
                .deferred_subclass_member_initializations
                .borrow_mut();
            let Some(deferred) = borrowed.pop() else {
                break
            };
            drop(borrowed);
            let cls = Class::from_non_generic_link(i_s.db, deferred.defined_at);
            debug!(
                "Calculate TypedDict members for deferred subclass {:?}",
                cls.name()
            );
            cls.initialize_typed_dict_members(i_s, deferred)
        }
    }

    fn enum_members(&self, i_s: &InferenceState) -> Box<[EnumMemberDefinition]> {
        let mut members = vec![];
        let mut name_indexes = vec![];
        for (name, name_index) in self
            .class_storage
            .class_symbol_table
            .iter_on_finished_table()
        {
            if name.starts_with('_') {
                if name == "__members__" {
                    let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
                    if !name_node_ref
                        .as_name()
                        .is_assignment_annotation_without_definition()
                    {
                        name_node_ref.add_issue(i_s, IssueKind::EnumMembersAttributeOverwritten)
                    }
                }
                continue;
            }
            name_indexes.push(name_index);
        }

        // The name indexes are not guarantueed to be sorted by its order in the tree. We however
        // want the original order in an enum.
        name_indexes.sort();

        for name_index in name_indexes {
            let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
            if name_node_ref
                .add_to_node_index(-(NAME_TO_FUNCTION_DIFF as i64))
                .maybe_function()
                .is_none()
            {
                let point = name_node_ref.point();
                if point.calculated() && point.kind() == PointKind::MultiDefinition {
                    NodeRef::new(self.node_ref.file, point.node_index()).add_issue(
                        i_s,
                        IssueKind::EnumReusedMemberName {
                            enum_name: self.name().into(),
                            member_name: name_node_ref.as_code().into(),
                        },
                    )
                }
                // TODO An enum member is never a descriptor. (that's how 3.10 does it). Here we
                // however only filter for functions and ignore decorators.
                members.push(EnumMemberDefinition::new(
                    StringSlice::from_name(self.node_ref.file_index(), name_node_ref.as_name())
                        .into(),
                    Some(name_node_ref.as_link()),
                ))
            }
        }
        members.into_boxed_slice()
    }

    fn gather_protocol_members(&self) -> Box<[ProtocolMember]> {
        let mut protocol_members = vec![];
        for (name, name_index) in self
            .class_storage
            .class_symbol_table
            .iter_on_finished_table()
        {
            if EXCLUDED_PROTOCOL_ATTRIBUTES.contains(&name) {
                continue;
            }
            let name_node_ref = NodeRef::new(self.node_ref.file, *name_index);
            protocol_members.push(ProtocolMember {
                name_index: *name_index,
                variance: match name_node_ref.as_name().expect_type() {
                    TypeLike::ImportFromAsName(_) | TypeLike::DottedAsName(_) => continue,
                    TypeLike::Function(_) => Variance::Covariant,
                    _ => Variance::Invariant,
                },
            })
        }
        protocol_members.sort_by_key(|member| member.name_index);
        protocol_members.into()
    }

    pub fn find_relevant_constructor(
        &self,
        i_s: &InferenceState<'db, '_>,
    ) -> NewOrInitConstructor<'_> {
        let (__init__, init_class, init_mro_index) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, "__init__", false);
        let (__new__, new_class, new_mro_index) =
            self.lookup_and_class_and_maybe_ignore_self_internal(i_s, "__new__", false);
        // This is just a weird heuristic Mypy uses, because the type system itself is very unclear
        // what to do if both __new__ and __init__ are present. So just only use __new__ if it's in
        // a lower MRO than an __init__.
        let is_new = new_mro_index < init_mro_index;
        NewOrInitConstructor {
            is_new,
            // TODO this should not be bound if is_new = false
            constructor: match is_new {
                false => __init__,
                true => __new__
                    .and_then(|inf| {
                        Some(inf.bind_new_descriptors(i_s, self, new_class.into_maybe_class()))
                    })
                    .unwrap(),
            },
            init_class: init_class.into_maybe_class(),
        }
    }

    pub(crate) fn execute(
        &self,
        original_i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> Inferred {
        if self.node_ref == original_i_s.db.python_state.dict_node_ref() {
            // This is a special case where we intercept the call to dict(..) when used with
            // TypedDict.
            if let Some(args_node_ref) = args.as_node_ref() {
                if let Some(inf) = args_node_ref
                    .file
                    .inference(original_i_s)
                    .infer_dict_call_from_context(args, result_context)
                {
                    return inf;
                }
            }
        }
        match self.execute_and_return_generics(
            original_i_s,
            args,
            result_context,
            on_type_error,
            from_type_type,
        ) {
            ClassExecutionResult::ClassGenerics(generics) => {
                let result = Inferred::from_type(Type::Class(GenericClass {
                    link: self.node_ref.as_link(),
                    generics,
                }));
                debug!("Class execute: {}", result.format_short(original_i_s));
                result
            }
            ClassExecutionResult::Inferred(inf) => inf,
        }
    }

    fn execute_and_return_generics(
        &self,
        original_i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> ClassExecutionResult {
        let i_s = &original_i_s.with_class_context(self);
        let had_type_error = Cell::new(false);
        let d = |_: &FunctionOrCallable, _: &Database| {
            had_type_error.set(true);
            Some(format!("\"{}\"", self.name()))
        };
        let on_type_error = on_type_error.with_custom_generate_diagnostic_string(&d);

        match &self.use_cached_class_infos(i_s.db).class_kind {
            ClassKind::Enum if self.node_ref.as_link() != i_s.db.python_state.enum_auto_link() => {
                // For whatever reason, auto is special, because it is somehow defined as an enum as
                // well, which is very weird.
                let metaclass =
                    Class::from_non_generic_link(i_s.db, i_s.db.python_state.enum_meta_link())
                        .instance();
                let call = metaclass
                    .type_lookup(i_s, |issue| args.add_issue(i_s, issue), "__call__")
                    .into_inferred()
                    .execute_with_details(i_s, args, result_context, on_type_error);
                if had_type_error.get() {
                    return ClassExecutionResult::Inferred(Inferred::new_any_from_error());
                }
                return ClassExecutionResult::Inferred(
                    execute_functional_enum(original_i_s, *self, args, result_context)
                        .unwrap_or_else(|| Inferred::new_any_from_error()),
                );
            }
            _ => (),
        }

        let constructor = self.find_relevant_constructor(i_s);
        if constructor.is_new {
            let result = constructor
                .constructor
                .into_inferred()
                .execute_with_details(i_s, args, result_context, on_type_error)
                .as_type(i_s);
            return match &result {
                // Only subclasses of the current class are valid, otherwise return the current
                // class. Diagnostics will care about these cases and raise errors when needed.
                Type::Class(c)
                    if self
                        .as_type(i_s.db)
                        .is_simple_super_type_of(i_s, &result)
                        .bool() =>
                {
                    ClassExecutionResult::Inferred(Inferred::from_type(result))
                }
                _ => ClassExecutionResult::ClassGenerics(self.generics_as_list(i_s.db)),
            };
        }

        match self.type_check_init_func(
            i_s,
            constructor.constructor,
            constructor.init_class,
            args,
            result_context,
            on_type_error,
            from_type_type,
        ) {
            Some(generics) => ClassExecutionResult::ClassGenerics(generics),
            None => ClassExecutionResult::Inferred(Inferred::new_any_from_error()),
        }
    }

    pub(crate) fn lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        self.lookup_with_details(i_s, add_issue, name, kind).lookup
    }

    pub(crate) fn lookup_with_details(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: impl Fn(IssueKind),
        name: &str,
        kind: LookupKind,
    ) -> LookupDetails<'a> {
        self.lookup_with_or_without_descriptors_internal(i_s, add_issue, name, kind, true, false)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        self.class_storage
            .parent_scope
            .qualified_name(db, self.node_ref, self.name())
    }

    pub fn name(&self) -> &'a str {
        self.node().name().as_str()
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match self.use_cached_class_infos(i_s.db).metaclass {
            MetaclassState::Some(_) => {
                if let Some(__getitem__) = self
                    .lookup(
                        i_s,
                        |issue| slice_type.as_node_ref().add_issue(i_s, issue),
                        "__getitem__",
                        LookupKind::OnlyType,
                    )
                    .into_maybe_inferred()
                {
                    return __getitem__.execute(i_s, &slice_type.as_args(*i_s));
                }
            }
            MetaclassState::Unknown => {
                todo!()
            }
            MetaclassState::None => (),
        }
        slice_type
            .file
            .inference(i_s)
            .compute_type_application_on_class(
                *self,
                *slice_type,
                matches!(result_context, ResultContext::AssignmentNewDefinition),
            )
    }

    pub fn in_slots(&self, db: &Database, name: &str) -> bool {
        for (_, type_or_class) in self.mro_maybe_without_object(db, true) {
            match type_or_class {
                TypeOrClass::Type(_) => (),
                TypeOrClass::Class(class) => {
                    if let Some(slots) = &class.class_storage.slots {
                        if slots.iter().any(|slot| {
                            let s = slot.as_str(db);
                            s == name || s == "__dict__"
                        }) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub(crate) fn check_slots(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) {
        for (_, type_or_class) in self.mro_maybe_without_object(i_s.db, true) {
            match type_or_class {
                TypeOrClass::Type(_) => (),
                TypeOrClass::Class(class) => {
                    let Some(slots) = &class.class_storage.slots else {
                        return
                    };
                    if class.lookup_symbol(i_s, "__setattr__").is_some() {
                        return;
                    }
                    if slots.iter().any(|slot| {
                        let s = slot.as_str(i_s.db);
                        s == name || s == "__dict__"
                    }) {
                        return;
                    }
                    if let Some(on_class) = class.lookup_symbol(i_s, name).into_maybe_inferred() {
                        if on_class
                            .as_cow_type(&i_s.with_class_context(&class))
                            .is_func_or_overload()
                        {
                            // Adds IssueType::CannotAssignToAMethod in other places.
                            return;
                        }
                    }
                }
            }
        }
        add_issue(IssueKind::AssigningToNameOutsideOfSlots {
            name: name.into(),
            class: self.format(&FormatData::with_style(i_s.db, FormatStyle::Qualified)),
        })
    }

    pub(crate) fn check_self_definition(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) {
        let (lookup, _, _) = self.lookup_and_class_and_maybe_ignore_self_internal(i_s, name, false);
        if let Some(inf) = lookup.into_maybe_inferred() {
            if inf.as_cow_type(i_s).is_func_or_overload_not_any_callable() {
                // See testSlotsAssignmentWithMethodReassign
                //add_issue(IssueType::CannotAssignToAMethod);
            }
        }
        self.check_slots(i_s, add_issue, name)
    }

    pub fn maybe_dataclass(&self) -> Option<Rc<Dataclass>> {
        // TODO this should probably not be needed.
        NodeRef::new(self.node_ref.file, self.node().name_definition().index())
            .complex()
            .and_then(|c| match c {
                ComplexPoint::TypeInstance(Type::Type(t)) => match t.as_ref() {
                    Type::Dataclass(d) => Some(d.clone()),
                    _ => None,
                },
                _ => None,
            })
    }

    pub fn maybe_typed_dict(&self) -> Option<Rc<TypedDict>> {
        self.maybe_typed_dict_definition()
            .map(|tdd| tdd.typed_dict())
    }

    pub fn maybe_typed_dict_definition(&self) -> Option<&TypedDictDefinition> {
        NodeRef::new(self.node_ref.file, self.node().name_definition().index())
            .complex()
            .and_then(|c| match c {
                ComplexPoint::TypedDictDefinition(tdd) => Some(tdd),
                _ => None,
            })
    }
}

impl fmt::Debug for Class<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file_index", &self.node_ref.file.file_index())
            .field("node_index", &self.node_ref.node_index)
            .field("name", &self.name())
            .field("generics", &self.generics)
            .field("type_var_remap", &self.type_var_remap)
            .finish()
    }
}

pub enum ClassExecutionResult {
    ClassGenerics(ClassGenerics),
    Inferred(Inferred),
}

#[derive(Debug, PartialEq)]
enum BaseKind {
    Class(PointLink),
    Dataclass(PointLink),
    NamedTuple(Rc<NamedTuple>),
    TypedDict(Rc<TypedDict>),
    Tuple(Rc<Tuple>),
    Type,
    Enum,
}

fn to_base_kind(t: &Type) -> BaseKind {
    match t {
        Type::Class(c) => BaseKind::Class(c.link),
        Type::Type(_) => BaseKind::Type,
        Type::Tuple(tup) => BaseKind::Tuple(tup.clone()),
        Type::Dataclass(d) => BaseKind::Dataclass(d.class.link),
        Type::TypedDict(d) => BaseKind::TypedDict(d.clone()),
        Type::NamedTuple(nt) => BaseKind::NamedTuple(nt.clone()),
        Type::Enum(_) => BaseKind::Enum,
        _ => unreachable!("{t:?}"),
    }
}

fn linearize_mro(i_s: &InferenceState, class: &Class, bases: &[Type]) -> Box<[BaseClass]> {
    let mut mro = vec![];

    let object = i_s.db.python_state.object_type();
    if let Some(index) = bases.iter().position(|base| base == &object) {
        // Instead of adding object to each iterator (because in our mro, object is not saved), we
        // just check for object in bases here. If it's not in the last position it's wrong.
        if index != bases.len() - 1 {
            add_inconsistency_issue(i_s, class)
        }
    }
    let mut add_to_mro =
        |base_index: usize, is_direct_base, new_base: &Type, allowed_to_use: &mut usize| {
            if new_base != &object {
                mro.push(BaseClass {
                    type_: if is_direct_base {
                        *allowed_to_use += 1;
                        new_base.clone()
                    } else {
                        new_base.replace_type_var_likes(i_s.db, &mut |t| {
                            bases[base_index].expect_class_generics()[t.index()].clone()
                        })
                    },
                    is_direct_base,
                })
            }
        };

    let mut base_iterators: Vec<_> = bases
        .iter()
        .map(|t| {
            let mut additional_type = None;
            let generic_class = match &t {
                Type::Class(c) => Some(c.class(i_s.db)),
                Type::Dataclass(d) => Some(d.class.class(i_s.db)),
                Type::Tuple(content) => {
                    let cls = i_s.db.python_state.tuple_class(i_s.db, content);
                    additional_type = Some(cls.as_type(i_s.db));
                    Some(cls)
                }
                Type::NamedTuple(nt) => {
                    let cls = i_s.db.python_state.tuple_class(i_s.db, &nt.as_tuple_ref());
                    additional_type = Some(cls.as_type(i_s.db));
                    Some(cls)
                }
                _ => None,
            };
            let super_classes = if let Some(cls) = generic_class {
                let cached_class_infos = cls.use_cached_class_infos(i_s.db);
                cached_class_infos.mro.as_ref()
            } else {
                &[]
            };
            std::iter::once(Cow::Borrowed(t))
                .chain(additional_type.into_iter().map(|t| Cow::Owned(t)))
                .chain(super_classes.iter().map(|base| Cow::Borrowed(&base.type_)))
                .enumerate()
                .peekable()
        })
        .collect();
    let mut linearizable = true;
    let mut allowed_to_use = 1;
    'outer: loop {
        let mut had_entry = false;
        for base_index in 0..allowed_to_use.min(bases.len()) {
            if let Some((i, candidate)) = base_iterators[base_index].peek().cloned() {
                had_entry = true;
                let conflicts = base_iterators.iter().any(|base_bases| {
                    base_bases
                        .clone()
                        .skip(1)
                        .any(|(_, other)| to_base_kind(&candidate) == to_base_kind(&other))
                });
                if !conflicts {
                    for base_bases in base_iterators.iter_mut() {
                        base_bases
                            .next_if(|(_, next)| to_base_kind(&candidate) == to_base_kind(next));
                    }
                    add_to_mro(base_index, i == 0, &candidate, &mut allowed_to_use);
                    continue 'outer;
                }
            }
        }
        if !had_entry {
            break;
        }
        for (base_index, base_bases) in base_iterators.iter_mut().enumerate() {
            if let Some((i, type_)) = base_bases.next() {
                // If it doesn't have to do with one of the first type, it is caused by
                // inconsistencies earlier.
                if bases.contains(&type_) {
                    linearizable = false;
                }
                add_to_mro(base_index, i == 0, &type_, &mut allowed_to_use);
                continue 'outer;
            }
        }
        unreachable!()
    }
    if !linearizable {
        add_inconsistency_issue(i_s, class)
    }
    mro.into_boxed_slice()
}

fn add_inconsistency_issue(i_s: &InferenceState, class: &Class) {
    NodeRef::new(
        class.node_ref.file,
        class.node().arguments().unwrap().index(),
    )
    .add_issue(
        i_s,
        IssueKind::InconsistentMro {
            name: class.name().into(),
        },
    );
}

pub struct MroIterator<'db, 'a> {
    db: &'db Database,
    generics: Generics<'a>,
    pub class: Option<TypeOrClass<'a>>,
    iterator: std::slice::Iter<'a, BaseClass>,
    mro_index: u32,
    pub returned_object: bool,
}

impl<'db, 'a> MroIterator<'db, 'a> {
    pub fn new(
        db: &'db Database,
        class: TypeOrClass<'a>,
        generics: Generics<'a>,
        iterator: std::slice::Iter<'a, BaseClass>,
        returned_object: bool,
    ) -> Self {
        Self {
            db,
            generics,
            class: Some(class),
            iterator,
            mro_index: 0,
            returned_object,
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeOrClass<'a> {
    Type(Cow<'a, Type>),
    Class(Class<'a>),
}

impl<'a> TypeOrClass<'a> {
    pub fn lookup_symbol<'db: 'a>(
        &'a self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
    ) -> (Option<Class<'a>>, LookupResult) {
        match self {
            Self::Class(class) => (Some(*class), class.lookup_symbol(i_s, name)),
            Self::Type(t) => t.lookup_symbol(i_s, name),
        }
    }

    pub fn name(&self, db: &'a Database) -> &str {
        match self {
            Self::Class(class) => class.name(),
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.class(db).name(),
                Type::NamedTuple(nt) => nt.name(db),
                Type::Tuple(_) => "Tuple",
                _ => todo!(),
            },
        }
    }

    pub fn into_maybe_class(self) -> Option<Class<'a>> {
        match self {
            TypeOrClass::Class(c) => Some(c),
            TypeOrClass::Type(_) => None,
        }
    }

    pub fn is_object(&self, db: &Database) -> bool {
        matches!(self, TypeOrClass::Class(c) if c.node_ref == db.python_state.object_node_ref())
    }

    pub fn originates_in_builtins_or_typing(&self, db: &Database) -> bool {
        match self {
            TypeOrClass::Class(c) => {
                let class_file_index = c.node_ref.file_index();
                class_file_index == db.python_state.builtins().file_index()
                    || c.node_ref.file_index() == db.python_state.typing().file_index()
            }
            TypeOrClass::Type(_) => true,
        }
    }
}

impl<'db: 'a, 'a> Iterator for MroIterator<'db, 'a> {
    type Item = (MroIndex, TypeOrClass<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.class.is_some() {
            self.mro_index += 1;
            Some((MroIndex(0), self.class.take().unwrap()))
        } else if let Some(c) = self.iterator.next() {
            let r = Some((
                MroIndex(self.mro_index),
                apply_generics_to_base_class(self.db, &c.type_, self.generics),
            ));
            self.mro_index += 1;
            r
        } else if !self.returned_object {
            self.returned_object = true;
            Some((
                MroIndex(self.mro_index),
                TypeOrClass::Class(self.db.python_state.object_class()),
            ))
        } else {
            None
        }
    }
}

impl<'db: 'a, 'a> DoubleEndedIterator for MroIterator<'db, 'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if !self.returned_object {
            self.returned_object = true;
            Some((
                MroIndex(self.mro_index),
                TypeOrClass::Class(self.db.python_state.object_class()),
            ))
        } else if let Some(c) = self.iterator.next_back() {
            let r = Some((
                MroIndex(self.mro_index),
                apply_generics_to_base_class(self.db, &c.type_, self.generics),
            ));
            self.mro_index += 1;
            r
        } else if self.class.is_some() {
            self.mro_index += 1;
            Some((MroIndex(0), self.class.take().unwrap()))
        } else {
            None
        }
    }
}

fn apply_generics_to_base_class<'a>(
    db: &'a Database,
    t: &'a Type,
    generics: Generics<'a>,
) -> TypeOrClass<'a> {
    match &t {
        Type::Class(g) => {
            let n = NodeRef::from_link(db, g.link);
            TypeOrClass::Class(match &g.generics {
                ClassGenerics::List(g) => Class::from_position(n, generics, Some(g)),
                ClassGenerics::None => Class::from_position(n, generics, None),
                ClassGenerics::ExpressionWithClassType(link) => todo!("Class::from_position(n, Generics::from_class_generics(self.db, t_generics), None)"),
                ClassGenerics::SlicesWithClassTypes(link) => todo!(),
                ClassGenerics::NotDefinedYet => unreachable!(),
            })
        }
        // TODO is this needed?
        //Type::RecursiveType(r) if matches!(r.origin(db), RecursiveTypeOrigin::Class(_)) => TypeOrClass::Class(Class::from_position(NodeRef::from_link(db, r.link), generics, r.generics.as_ref())),
        // TODO this is wrong, because it does not use generics.
        _ if matches!(generics, Generics::None | Generics::NotDefinedYet) => {
            TypeOrClass::Type(Cow::Borrowed(t))
        }
        _ => TypeOrClass::Type(Cow::Owned(t.replace_type_var_likes_and_self(
            db,
            &mut |usage| generics.nth_usage(db, &usage).into_generic_item(db),
            &|| todo!(),
        ))),
    }
}

fn find_stmt_named_tuple_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut Vec<CallableParam>,
    simple_stmts: SimpleStmts,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name), annot, default) => {
                    if default.is_none() && vec.last().is_some_and(|last| last.has_default) {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueKind::NamedTupleNonDefaultFieldFollowsDefault);
                        continue;
                    }
                    file.inference(i_s)
                        .ensure_cached_named_tuple_annotation(annot);
                    let t = use_cached_annotation_type(i_s.db, file, annot).into_owned();
                    if name.as_code().starts_with('_') {
                        NodeRef::new(file, name.index()).add_issue(
                            i_s,
                            IssueKind::NamedTupleNameCannotStartWithUnderscore {
                                field_name: name.as_code().into(),
                            },
                        )
                    } else {
                        vec.push(CallableParam {
                            type_: ParamType::PositionalOrKeyword(t),
                            has_default: default.is_some(),
                            name: Some(
                                StringSlice::from_name(file.file_index(), name.name()).into(),
                            ),
                        })
                    }
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueKind::InvalidStmtInNamedTuple),
            },
            _ => (),
        }
    }
}

fn find_stmt_typed_dict_types(
    i_s: &InferenceState,
    file: &PythonFile,
    vec: &mut TypedDictMemberGatherer,
    simple_stmts: SimpleStmts,
    total: bool,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(Target::Name(name_def), annot, right_side) => {
                    if right_side.is_some() {
                        NodeRef::new(file, assignment.index())
                            .add_issue(i_s, IssueKind::TypedDictInvalidMemberRightSide);
                    }
                    if let Err(issue) = vec.add(
                        i_s.db,
                        file.inference(i_s).compute_class_typed_dict_member(
                            StringSlice::from_name(file.file_index(), name_def.name()),
                            annot,
                            total,
                        ),
                    ) {
                        NodeRef::new(file, assignment.index()).add_issue(i_s, issue);
                    }
                }
                AssignmentContent::Normal(targets, _) => {
                    NodeRef::new(file, assignment.index())
                        .add_issue(i_s, IssueKind::TypedDictInvalidMember);
                    for target in targets {
                        if let Target::Name(name_def) = target {
                            // Add those names regardless, because an error was already added.
                            vec.add(
                                i_s.db,
                                TypedDictMember {
                                    type_: Type::Any(AnyCause::Todo),
                                    required: true,
                                    name: StringSlice::from_name(
                                        file.file_index(),
                                        name_def.name(),
                                    ),
                                },
                            )
                            .ok();
                        }
                    }
                }
                _ => NodeRef::new(file, assignment.index())
                    .add_issue(i_s, IssueKind::TypedDictInvalidMember),
            },
            _ => (),
        }
    }
}

fn add_protocol_mismatch(
    i_s: &InferenceState,
    notes: &mut Vec<Box<str>>,
    name: &str,
    t1: &Type,
    t2: &Type,
    full1: &Type,
    full2: &Type,
) {
    match (full1, full2) {
        (
            Type::Callable(_) | Type::FunctionOverload(_),
            Type::Callable(_) | Type::FunctionOverload(_) | Type::Type(_),
        ) => {
            notes.push("    Expected:".into());
            let c1 = full1.maybe_callable(i_s).unwrap();
            let c2 = full2.maybe_callable(i_s).unwrap();
            format_callable_like(i_s.db, notes, &c1, &c2);
            notes.push("    Got:".into());
            format_callable_like(i_s.db, notes, &c2, &c1);
        }
        _ => notes.push(
            format!(
                r#"    {name}: expected "{}", got "{}""#,
                t1.format(&FormatData::with_style(i_s.db, FormatStyle::Short)),
                t2.format(&FormatData::with_style(i_s.db, FormatStyle::Short))
            )
            .into(),
        ),
    }
}

fn protocol_conflict_note(db: &Database, other: &Type) -> Box<str> {
    match other {
        Type::Module(file_index) => format!(
            "Following member(s) of Module \"{}\" have conflicts:",
            Module::from_file_index(db, *file_index).qualified_name(db)
        ),
        Type::Type(t) => format!(
            "Following member(s) of \"{}\" have conflicts:",
            t.format_short(db)
        ),
        _ => format!(
            "Following member(s) of \"{}\" have conflicts:",
            other.format_short(db)
        ),
    }
    .into()
}

fn format_callable_like(
    db: &Database,
    notes: &mut Vec<Box<str>>,
    c: &CallableLike,
    other: &CallableLike,
) {
    let other_had_first_annotation = other.had_first_self_or_class_annotation();
    let prefix = "        ";
    let format_callable = |c: &CallableContent| {
        format!(
            "{prefix}{}",
            c.format_pretty_detailed(
                &FormatData::new_short(db),
                !c.kind.had_first_self_or_class_annotation() && !other_had_first_annotation,
                false,
            )
        )
    };

    match c {
        CallableLike::Callable(c) => notes.push(format_callable(&c).into()),
        CallableLike::Overload(o) => {
            for c in o.iter_functions() {
                notes.push(format!("{prefix}@overload").into());
                notes.push(format_callable(&c).into());
            }
        }
    }
}

pub struct NewOrInitConstructor<'a> {
    // A data structure to show wheter __init__ or __new__ is the relevant constructor for a class
    constructor: LookupResult,
    init_class: Option<Class<'a>>,
    is_new: bool,
}

impl NewOrInitConstructor<'_> {
    pub fn maybe_callable(self, i_s: &InferenceState, cls: Class) -> Option<CallableLike> {
        let inf = self.constructor.into_inferred();
        if self.is_new {
            inf.as_cow_type(i_s).maybe_callable(i_s).map(
                |callable_like| /*match self.init_class {
                                       // TODO probably enable??
                    Some(class) => match callable_like {
                        CallableLike::Callable(c) => {
                            CallableLike::Callable(Rc::new(c.merge_class_type_vars(
                                i_s.db,
                                class,
                                class,
                            )))
                        }
                        CallableLike::Overload(overload) => CallableLike::Overload(FunctionOverload::new(overload.iter_functions().map(|c| {
                            c.merge_class_type_vars(
                                i_s.db,
                                class,
                                class,
                            )
                        }).collect()))
                    },
                    None => */callable_like, /*}*/
            )
        } else {
            let cls = if matches!(cls.generics(), Generics::NotDefinedYet) {
                Class::with_self_generics(i_s.db, cls.node_ref)
            } else {
                cls
            };
            let callable = if let Some(c) = self.init_class {
                let i_s = &i_s.with_class_context(&c);
                inf.as_cow_type(i_s).maybe_callable(i_s)
            } else {
                inf.as_cow_type(i_s).maybe_callable(i_s)
            };
            let to_callable = |c: &CallableContent| {
                // Since __init__ does not have a return, We need to check the params
                // of the __init__ functions and the class as a return type separately.
                c.remove_first_param().map(|mut c| {
                    let self_ = cls.as_type(i_s.db);
                    let needs_type_var_remap = self.init_class.is_some_and(|c| {
                        !c.type_vars(i_s).is_empty() && c.node_ref != cls.node_ref
                    });

                    // If the __init__ comes from a super class, we need to fetch the generics that
                    // are relevant for our class.
                    if c.has_self_type() || needs_type_var_remap {
                        c = c.replace_type_var_likes_and_self(
                            i_s.db,
                            &mut |usage| {
                                if needs_type_var_remap {
                                    if let Some(func_class) = self.init_class {
                                        if let Some(result) =
                                            maybe_class_usage(i_s.db, &func_class, &usage)
                                        {
                                            return result;
                                        }
                                    }
                                }
                                usage.into_generic_item()
                            },
                            &|| self_.clone(),
                        )
                    }
                    c.return_type = self_;

                    // Now we have two sets of generics, the generics for the class and the
                    // generics for the __init__ function. We merge those and then set the proper
                    // ids for the type vars.
                    let class_type_vars = cls.type_vars(i_s);
                    if class_type_vars.is_empty() {
                        c.type_vars = class_type_vars.clone();
                    } else {
                        let mut tv_vec = class_type_vars.as_vec();
                        tv_vec.extend(c.type_vars.iter().cloned());
                        c.type_vars = TypeVarLikes::from_vec(tv_vec);
                    }
                    if !c.type_vars.is_empty() {
                        c = c.replace_type_var_likes_and_self(
                            i_s.db,
                            &mut |mut usage| {
                                let in_def = usage.in_definition();
                                if cls.node_ref.as_link() == in_def {
                                    usage.update_in_definition_and_index(
                                        c.defined_at,
                                        usage.index(),
                                    );
                                } else if c.defined_at == in_def {
                                    usage.update_in_definition_and_index(
                                        c.defined_at,
                                        (class_type_vars.len() + usage.index().as_usize()).into(),
                                    )
                                }
                                usage.into_generic_item()
                            },
                            &|| unreachable!("was already replaced above"),
                        );
                    }
                    Rc::new(c)
                })
            };
            callable.and_then(|callable_like| match callable_like {
                CallableLike::Callable(c) => to_callable(&c).map(|c| CallableLike::Callable(c)),
                CallableLike::Overload(callables) => {
                    let funcs: Box<_> = callables
                        .iter_functions()
                        .filter_map(|c| to_callable(c))
                        .collect();
                    match funcs.len() {
                        0 | 1 => todo!(),
                        _ => Some(CallableLike::Overload(FunctionOverload::new(funcs))),
                    }
                }
            })
        }
    }

    fn as_type(self, i_s: &InferenceState, cls: Class) -> Option<Type> {
        self.maybe_callable(i_s, cls).map(|x| match x {
            CallableLike::Callable(c) => Type::Callable(c),
            CallableLike::Overload(o) => Type::FunctionOverload(o),
        })
    }
}

pub fn start_namedtuple_params(db: &Database) -> Vec<CallableParam> {
    vec![CallableParam {
        type_: ParamType::PositionalOnly(db.python_state.type_of_self.clone()),
        has_default: false,
        name: None,
    }]
}
