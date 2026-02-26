use std::{
    borrow::Cow,
    cell::{Cell, RefCell},
    fmt,
    sync::Arc,
};

use parsa_python_cst::{Assignment, AssignmentContent, AtomContent, ClassDef, Name, TypeLike};

use super::{Callable, Instance, InstanceLookupOptions, LookupDetails, overload::OverloadResult};
use crate::{
    arguments::{ArgKind, Args},
    database::{
        BaseClass, ClassKind, ClassStorage, ComplexPoint, Database, Locality, MetaclassState,
        ParentScope, Point, PointKind, PointLink, Specific,
    },
    debug,
    diagnostics::IssueKind,
    file::{
        ClassInitializer, ClassNodeRef, FLOW_ANALYSIS, FuncNodeRef, TypeVarCallbackReturn,
        use_cached_return_annotation_type,
    },
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{
        ApplyClassDescriptorsOrigin, AttributeKind, FunctionOrOverload, Inferred, MroIndex,
    },
    match_::{Match, MismatchReason},
    matching::{
        ErrorStrs, Generic, Generics, LookupKind, Matcher, OnTypeError,
        calc_callable_dunder_init_type_vars, calc_callable_type_vars,
        calc_class_dunder_init_type_vars, format_got_expected, maybe_class_usage,
    },
    node_ref::NodeRef,
    recoverable_error,
    result_context::ResultContext,
    type_::{
        AnyCause, CallableContent, CallableLike, CallableParam, CallableParams, ClassGenerics,
        Dataclass, DbString, Enum, FormatStyle, FunctionOverload, GenericClass, GenericItem,
        GenericsList, LiteralValue, LookupResult, NamedTuple, NeverCause, ParamSpecArg,
        ParamSpecUsage, ParamType, ReplaceTypeVarLikes, StarParamType, StringSlice, Tuple,
        TupleArgs, Type, TypeVarIndex, TypeVarLike, TypeVarLikeUsage, TypeVarLikes, TypedDict,
        TypedDictGenerics, Variance, add_any_params_to_params,
    },
    type_helpers::FuncLike,
    utils::{debug_indent, is_magic_method},
};

pub fn cache_class_name(name_def: NodeRef, class: ClassDef) {
    if !name_def.point().calculated() {
        name_def.set_point(Point::new_redirect(
            name_def.file_index(),
            class.index(),
            Locality::Todo,
        ));
    }
}

impl<'a> std::ops::Deref for Class<'a> {
    type Target = ClassNodeRef<'a>;

    fn deref(&self) -> &Self::Target {
        &self.node_ref
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Class<'a> {
    pub node_ref: ClassNodeRef<'a>,
    pub class_storage: &'a ClassStorage,
    pub generics: Generics<'a>,
    type_var_remap: Option<&'a GenericsList>,
}

impl<'db: 'a, 'a> Class<'a> {
    pub fn new(
        node_ref: ClassNodeRef<'a>,
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
        let class_ref = ClassNodeRef::from_link(db, link);
        let generics = Generics::from_class_generics(db, class_ref, list);
        Self::from_position(class_ref, generics, None)
    }

    pub fn from_non_generic_link(db: &'db Database, link: PointLink) -> Self {
        Self::from_non_generic_node_ref(ClassNodeRef::from_link(db, link))
    }

    pub fn from_non_generic_node_ref(node_ref: ClassNodeRef<'db>) -> Self {
        Self::from_position(node_ref, Generics::None, None)
    }

    #[inline]
    pub fn from_position(
        node_ref: ClassNodeRef<'a>,
        generics: Generics<'a>,
        type_var_remap: Option<&'a GenericsList>,
    ) -> Self {
        Self::new(node_ref, node_ref.class_storage(), generics, type_var_remap)
    }

    #[inline]
    pub fn from_undefined_generics(db: &'db Database, link: PointLink) -> Self {
        let class_ref = ClassNodeRef::from_link(db, link);
        Self::with_undefined_generics(class_ref)
    }

    #[inline]
    pub fn with_undefined_generics(class_ref: ClassNodeRef<'a>) -> Self {
        Self::from_position(class_ref, Generics::NotDefinedYet { class_ref }, None)
    }

    pub fn with_self_generics(db: &'a Database, node_ref: ClassNodeRef<'a>) -> Self {
        let type_var_likes = node_ref.use_cached_type_vars(db);
        Self::from_position(
            node_ref,
            match type_var_likes.is_empty() {
                true => Generics::None,
                false => Generics::Self_ {
                    class_ref: node_ref,
                },
            },
            None,
        )
    }

    pub fn instance(self) -> Instance<'a> {
        Instance::new(self, None)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        ClassInitializer::new(self.node_ref, self.class_storage).qualified_name(db)
    }

    pub(crate) fn find_type_var_like_including_ancestors(
        &self,
        db: &Database,
        type_var_like: &TypeVarLike,
        class_seen: bool,
    ) -> Option<TypeVarCallbackReturn> {
        ClassInitializer::new(self.node_ref, self.class_storage)
            .find_type_var_like_including_ancestors(db, type_var_like, class_seen)
    }

    fn type_check_dunder_init_func(
        &self,
        i_s: &InferenceState<'db, '_>,
        __init__: LookupResult,
        dunder_init_class: TypeOrClass,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool, // Errors are different for Cls() vs. Type[Cls] that is instantiated
    ) -> ClassExecutionResult {
        let Some(inf) = __init__.into_maybe_inferred() else {
            if self.is_protocol(i_s.db) {
                if !from_type_type {
                    args.add_issue(
                        i_s,
                        IssueKind::CannotInstantiateProtocol {
                            name: self.name().into(),
                        },
                    );
                }
            } else {
                debug_assert!(self.incomplete_mro(i_s.db));
            }
            let type_var_likes = self.type_vars(i_s);
            return ClassExecutionResult::ClassGenerics(match type_var_likes.is_empty() {
                false => ClassGenerics::List(type_var_likes.as_any_generic_list()),
                true => ClassGenerics::new_none(),
            });
        };
        match inf.init_as_function(i_s, dunder_init_class.maybe_class()) {
            FunctionOrOverload::Function(func) => {
                /*
                let type_vars = self.type_vars(i_s);
                if let Some(func_cls) = &mut func.class {
                    if func_cls.type_var_remap.is_some() && matches!(func_cls.generics, Generics::NotDefinedYet) {
                        func_cls.generics = Generics::Self_ { class_definition: self.node_ref.as_link(), type_var_likes: &type_vars }
                    }
                }
                */

                let calculated_type_args = calc_class_dunder_init_type_vars(
                    i_s,
                    self,
                    func,
                    args.iter(i_s.mode),
                    |issue| args.add_issue(i_s, issue),
                    result_context,
                    on_type_error,
                );
                ClassExecutionResult::ClassGenerics(
                    calculated_type_args.type_arguments_into_class_generics(i_s.db),
                )
            }
            FunctionOrOverload::Callable(callable_content) => {
                let calculated_type_args = match dunder_init_class.as_base_class(i_s.db, self) {
                    Some(class) => {
                        let from_class = matches!(dunder_init_class, TypeOrClass::Class(_));
                        calc_callable_dunder_init_type_vars(
                            i_s,
                            self,
                            Callable::new(&callable_content, from_class.then_some(class)),
                            args.iter(i_s.mode),
                            |issue| args.add_issue(i_s, issue),
                            from_class,
                            result_context,
                            Some(on_type_error),
                        )
                    }
                    // Happens for example when NamedTuples are involved.
                    None => calc_callable_type_vars(
                        i_s,
                        Callable::new(&callable_content, Some(*self)),
                        args.iter(i_s.mode),
                        |issue| args.add_issue(i_s, issue),
                        false,
                        result_context,
                        None,
                        Some(on_type_error),
                    ),
                };
                ClassExecutionResult::ClassGenerics(
                    calculated_type_args.type_arguments_into_class_generics(i_s.db),
                )
            }
            FunctionOrOverload::Overload(overloaded_function) => match overloaded_function
                .find_matching_function(
                    i_s,
                    args,
                    false,
                    Some(self),
                    true,
                    result_context,
                    None,
                    on_type_error,
                    &|_, calculated_type_args| {
                        Type::new_class(
                            self.node_ref.as_link(),
                            calculated_type_args.type_arguments_into_class_generics(i_s.db),
                        )
                    },
                ) {
                OverloadResult::Single(callable) => {
                    // Execute the found function to create the diagnostics.
                    let result = calc_callable_dunder_init_type_vars(
                        i_s,
                        self,
                        callable,
                        args.iter(i_s.mode),
                        |issue| args.add_issue(i_s, issue),
                        true,
                        result_context,
                        Some(on_type_error),
                    );
                    ClassExecutionResult::ClassGenerics(
                        result.type_arguments_into_class_generics(i_s.db),
                    )
                }
                OverloadResult::Union(t) => ClassExecutionResult::Inferred(Inferred::from_type(t)),
                OverloadResult::NotFound => {
                    ClassExecutionResult::Inferred(Inferred::new_any_from_error())
                }
            },
        }
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
        self.use_cached_class_infos(db).kind == ClassKind::Protocol
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
        let positional_default = i_s.db.mypy_compatible();
        matcher.ignore_positional_param_names = positional_default;

        let mut protocol_member_count = 0;
        for (_, c) in self.mro_maybe_without_object(i_s.db, true) {
            let TypeOrClass::Class(c) = c else {
                debug!("Ignored a type in protocol mro. Why is it there in the first place?");
                continue;
            };
            let protocol_members = &c.use_cached_class_infos(i_s.db).protocol_members;
            protocol_member_count += protocol_members.len();
            for protocol_member in protocol_members.iter() {
                let name = NodeRef::new(c.node_ref.file, protocol_member.name_index).as_code();
                // It is possible to match a Callable against a Protocol that only implements
                // __call__.
                let is_call = name == "__call__";
                let mut mismatch = false;
                let had_error = RefCell::new(None);
                if is_call {
                    // __call__ matching doesn't ignore param names, matching all other methods
                    // does.
                    matcher.ignore_positional_param_names = false;
                    if !matches!(other, Type::Class(_)) {
                        let inf1 = Instance::new(c, None)
                            .type_lookup(
                                i_s,
                                |issue| {
                                    let issue_str = self.node_ref.issue_to_str(i_s, issue);
                                    debug!("Issue in protocol __call__: {issue_str}");
                                    *had_error.borrow_mut() = Some(issue_str);
                                },
                                name,
                            )
                            .into_inferred();
                        //Iterable[_T] :> EnumMeta Type[_EnumMemberT] :> EnumMeta
                        if inf1
                            .as_cow_type(i_s)
                            .matches(i_s, matcher, other, protocol_member.variance)
                            .bool()
                            && had_error.borrow().is_none()
                        {
                            matcher.ignore_positional_param_names = positional_default;
                            had_at_least_one_member_with_same_name = true;
                            continue;
                        }
                        mismatch = true;
                    }
                }

                let had_binding_error = Cell::new(false);
                let mut had_lookup_error = false;
                let protocol_lookup_details = Instance::new(c, None).lookup(
                    i_s,
                    name,
                    InstanceLookupOptions::new(&|_| had_binding_error.set(true))
                        .with_as_self_instance(&|| other.clone())
                        .with_avoid_inferring_return_types(),
                );
                let protocol_inf = protocol_lookup_details.lookup.into_inferred();

                // It's a bit weird that we have to filter out TypeVarLikes here, but at the moment
                // there is no way to have that information when we gather Protocol members.
                if matches!(
                    protocol_inf.maybe_complex_point(i_s.db),
                    Some(ComplexPoint::TypeVarLike(_))
                ) {
                    continue;
                }

                other.run_after_lookup_on_each_union_member(
                    i_s,
                    None,
                    self.node_ref.file,
                    name,
                    // Magic methods are probably never relevant on the object, since Python
                    // ignores all self attributes. This is especially the case if Enums classes
                    // are passed. However it feels a bit weird here and might need to be changed
                    // in the future.
                    if is_magic_method(name) {
                        LookupKind::OnlyType
                    } else {
                        LookupKind::Normal
                    },
                    &mut ResultContext::Unknown,
                    &|issue| {
                        // Deprecated should not affect matching
                        if let IssueKind::Deprecated { .. } = &issue {
                            return;
                        }
                        let issue_str = self.node_ref.issue_to_str(i_s, issue);
                        debug!("Issue in protocol: {}", issue_str);
                        *had_error.borrow_mut() = Some(issue_str);
                    },
                    &mut |_, mut lookup_details| {
                        if name == "__hash__"
                            && other.is_protocol(i_s.db)
                            && lookup_details.class.is_object(i_s.db)
                        {
                            // __hash__ can be overwritten with None
                            lookup_details.lookup = LookupResult::None;
                        }
                        if matches!(lookup_details.lookup, LookupResult::None) {
                            had_lookup_error = true;
                        } else if had_error.borrow().is_none() {
                            had_at_least_one_member_with_same_name = true;
                            let protocol_t = protocol_inf.as_cow_type(i_s);
                            let lookup = lookup_details.lookup.into_inferred();
                            let t2 = lookup.as_cow_type(i_s);
                            let other_setter_type = lookup_details.attr_kind.property_setter_type();
                            let mut variance = protocol_member.variance;
                            if other_setter_type.is_some() {
                                // Check protocols with setters separately below
                                variance = Variance::Covariant
                            }
                            let m = protocol_t.matches(i_s, matcher, &t2, variance);

                            let is_final_mismatch = lookup_details.attr_kind == AttributeKind::Final
                                && protocol_lookup_details.attr_kind != AttributeKind::Final;

                            let mut maybe_add_conflict_note = |notes: &mut Vec<_>| {
                                if !had_conflict_note {
                                    had_conflict_note = true;
                                    notes.push(protocol_conflict_note(i_s.db, other));
                                }
                            };
                            if (!m.bool()
                                    || (is_call && !matches!(other, Type::Class(_)))
                                    || had_binding_error.get()
                                )
                                // is_final_mismatch errors will be added later
                                && !is_final_mismatch
                            {
                                maybe_add_conflict_note(&mut notes);
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    match other.maybe_class(i_s.db) {
                                        Some(cls) => add_protocol_mismatch(
                                            i_s,
                                            &mut notes,
                                            name,
                                            &protocol_t,
                                            &t2,
                                            &c.lookup(i_s, name, ClassLookupOptions::new(&|_| ())
                                                    .with_as_type_type(&|| if other.is_subclassable(i_s.db) {
                                                        Type::Type(Arc::new(other.clone()))
                                                    } else {
                                                        self.as_type_type(i_s.db)
                                                    })
                                                )
                                                .lookup
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                            &cls.simple_lookup(i_s, |_| (), name)
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                        ),
                                        None => {
                                            let full_other = match other {
                                                Type::Type(t) if is_call => {
                                                    t.maybe_class(i_s.db).and_then(|cls| {
                                                        notes.push(format!(
                                                            r#""{}" has constructor incompatible with "__call__" of "{}""#,
                                                            cls.name(),
                                                            self.name()
                                                        ).into());
                                                        cls.find_relevant_constructor(i_s, &|_| ())
                                                            .into_type(i_s, cls)
                                                    })
                                                }
                                                _ => None,
                                            };
                                            add_protocol_mismatch(
                                                i_s,
                                                &mut notes,
                                                name,
                                                &protocol_t,
                                                &t2,
                                                &protocol_t,
                                                full_other.as_ref().unwrap_or(&t2),
                                            )
                                        }
                                    }
                                }
                            }

                            let proto_setter_type = protocol_lookup_details.attr_kind.property_setter_type();
                            if other_setter_type.is_some() || proto_setter_type.is_some() {
                                let o_t = other_setter_type.unwrap_or(&t2);
                                let p_t = proto_setter_type.unwrap_or(&protocol_t);
                                if !p_t.is_sub_type_of(i_s, matcher, o_t).bool() {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        maybe_add_conflict_note(&mut notes);
                                        notes.push(
                                            format!(
                                                r#"    {name}: expected setter type "{}", got "{}""#,
                                                p_t.format_short(i_s.db),
                                                o_t.format_short(i_s.db),
                                            )
                                            .into(),
                                        );
                                        if p_t.is_super_type_of(i_s, matcher, o_t).bool() {
                                            notes.push("    Setter types should behave contravariantly".into());
                                        }
                                    }
                                }
                            }

                            if lookup_details.attr_kind.is_read_only_property()
                                && !protocol_lookup_details.attr_kind.is_read_only_property()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected settable variable, \
                                         got read-only attribute",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }

                            if matches!(protocol_lookup_details.attr_kind, AttributeKind::ClassVar) {
                                if !matches!(lookup_details.attr_kind, AttributeKind::ClassVar)
                                {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                                "Protocol member {}.{name} expected class variable, \
                                             got instance variable",
                                                self.name()
                                            )
                                            .into(),
                                        );
                                    }
                                } else if other.maybe_type_of_class(i_s.db).is_some() {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                                "ClassVar protocol member {}.{name} can never be \
                                                 matched by a class object",
                                                self.name()
                                            )
                                            .into(),
                                        );
                                    }
                                }
                            }

                            if matches!(lookup_details.attr_kind, AttributeKind::ClassVar)
                               && !protocol_lookup_details.attr_kind.classvar_like()
                               && other.maybe_class(i_s.db).is_some()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                            "Protocol member {}.{name} expected instance variable, \
                                         got class variable",
                                            self.name()
                                        )
                                        .into(),
                                    );
                                }
                            }
                            if protocol_lookup_details
                                .attr_kind
                                .classmethod_or_staticmethod()
                                && !lookup_details.attr_kind.classmethod_or_staticmethod()
                            {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected class or static method",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }
                            if lookup_details.attr_kind == AttributeKind::AnnotatedAttribute
                                && let Type::Type(t) = other {
                                    mismatch = true;
                                    if mismatches < SHOW_MAX_MISMATCHES {
                                        notes.push(
                                            format!(
                                            "Only class variables allowed for class object access \
                                             on protocols, {name} is an instance variable of \"{}\"",
                                            t.format_short(i_s.db),
                                        )
                                            .into(),
                                        );
                                    }
                                }
                            if is_final_mismatch {
                                mismatch = true;
                                if mismatches < SHOW_MAX_MISMATCHES {
                                    notes.push(
                                        format!(
                                        "Protocol member {}.{name} expected settable variable, \
                                         got read-only attribute",
                                        self.name()
                                    )
                                        .into(),
                                    );
                                }
                            }
                        }
                    },
                );
                if let Some(issue) = had_error.take() {
                    if mismatches < SHOW_MAX_MISMATCHES {
                        notes.push(issue.into());
                    }
                    mismatch = true;
                }
                if had_lookup_error {
                    missing_members.push(name);
                }
                if is_call {
                    matcher.ignore_positional_param_names = positional_default;
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

    pub fn non_method_protocol_members(&self, db: &Database) -> Vec<String> {
        let mut members = vec![];
        for (_, c) in self.mro_maybe_without_object(db, true) {
            let TypeOrClass::Class(c) = c else { continue };
            let protocol_members = &c.use_cached_class_infos(db).protocol_members;
            for protocol_member in protocol_members.iter() {
                let name_node_ref = NodeRef::new(self.node_ref.file, protocol_member.name_index);
                if !matches!(
                    name_node_ref.expect_name().expect_type(),
                    TypeLike::Function(_)
                ) {
                    members.push(name_node_ref.as_code().into())
                }
            }
        }
        members
    }

    pub fn lookup_assignment(&self, name: &str) -> Option<Assignment<'a>> {
        let i = self.class_storage.class_symbol_table.lookup_symbol(name)?;
        NodeRef::new(self.node_ref.file, i)
            .expect_name()
            .maybe_assignment_definition_name()
    }

    pub fn lookup_symbol(&self, i_s: &InferenceState<'db, '_>, name: &str) -> LookupResult {
        match self.class_storage.class_symbol_table.lookup_symbol(name) {
            None => {
                for star_import in self.node_ref.file.star_imports.iter() {
                    if star_import.scope == self.node_ref.node_index {
                        let self_class = Class::with_self_generics(i_s.db, self.node_ref);
                        let i_s = &i_s.with_class_context(&self_class);
                        if let Some(result) = self
                            .node_ref
                            .file
                            .name_resolution_for_inference(i_s)
                            .lookup_name_in_star_import(star_import, name, true, None)
                        {
                            return result.into_lookup_result(i_s);
                        }
                    }
                }
                LookupResult::None
            }
            Some(node_index) => {
                let self_class = Class::with_self_generics(i_s.db, self.node_ref);
                let i_s = &i_s.with_class_context(&self_class);
                let node_ref = NodeRef::new(self.node_ref.file, node_index);
                if node_ref.point().needs_flow_analysis()
                    && !node_ref.name_def_ref_of_name().point().calculated()
                    && let Err(()) = self.ensure_calculated_diagnostics_for_class(i_s.db)
                {
                    return LookupResult::None;
                }
                let inf = node_ref.infer_name_of_definition_by_index(i_s);
                LookupResult::GotoName {
                    name: PointLink::new(self.node_ref.file.file_index, node_index),
                    inf,
                }
            }
        }
    }

    fn lookup_and_class_and_maybe_ignore_self_internal<T>(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        super_count: usize,
        without_object: bool,
        bind: impl FnOnce(LookupResult, TypeOrClass<'a>, MroIndex) -> T,
    ) -> T {
        if name == "__doc__" {
            let t = if self.node().docstring().is_some() {
                i_s.db.python_state.str_type()
            } else {
                Type::None
            };
            return bind(
                LookupResult::UnknownName(Inferred::from_type(t)),
                TypeOrClass::Class(*self),
                0.into(),
            );
        }
        for (mro_index, c) in self
            .mro_maybe_without_object(i_s.db, self.incomplete_mro(i_s.db) || without_object)
            .skip(super_count)
        {
            let (_, result) = c.lookup_symbol(i_s, name);
            if !matches!(result, LookupResult::None) {
                return match &c {
                    // TODO why?
                    TypeOrClass::Type(t) if matches!(t.as_ref(), Type::NamedTuple(_)) => bind(
                        result,
                        TypeOrClass::Class(i_s.db.python_state.typing_named_tuple_class(i_s.db)),
                        mro_index,
                    ),
                    _ => bind(result, c.clone(), mro_index),
                };
            }
        }
        bind(
            LookupResult::None,
            TypeOrClass::Type(Cow::Borrowed(&Type::Any(AnyCause::Internal))),
            0.into(),
        )
    }

    pub fn lookup(
        &self,
        i_s: &InferenceState<'db, '_>,
        name: &str,
        options: ClassLookupOptions,
    ) -> LookupDetails<'a> {
        let class_infos = self.use_cached_class_infos(i_s.db);

        let lookup_on_metaclass = |ignore_no_metaclass: bool| {
            let metaclass_result = match class_infos.metaclass {
                MetaclassState::Unknown => LookupDetails::any(AnyCause::Todo),
                MetaclassState::None if ignore_no_metaclass => return LookupDetails::none(),
                _ => {
                    let instance = Instance::new(class_infos.metaclass(i_s.db), None);
                    instance.lookup(
                        i_s,
                        name,
                        InstanceLookupOptions::new(options.add_issue).with_as_self_instance(
                            options
                                .as_type_type
                                .unwrap_or(&|| self.as_type_type(i_s.db)),
                        ),
                    )
                }
            };
            if matches!(&metaclass_result.lookup, LookupResult::None) && self.incomplete_mro(i_s.db)
            {
                LookupDetails::any(AnyCause::Todo)
            } else {
                LookupDetails {
                    class: TypeOrClass::Class(*self),
                    lookup: metaclass_result.lookup,
                    // The AttributeKind changes, because it's the metaclass and it kind of becomes
                    // a ClassVar
                    attr_kind: match metaclass_result.attr_kind {
                        AttributeKind::Attribute | AttributeKind::AnnotatedAttribute => {
                            AttributeKind::ClassVar
                        }
                        k => k,
                    },
                    mro_index: None,
                }
            }
        };

        let result = if options.kind == LookupKind::Normal {
            if class_infos.kind == ClassKind::Enum
                && options.apply_descriptors_origin.should_apply()
                && name == "_ignore_"
            {
                return LookupDetails {
                    lookup: LookupResult::None,
                    class: TypeOrClass::Class(*self),
                    attr_kind: AttributeKind::Attribute,
                    mro_index: None,
                };
            }
            self.lookup_and_class_and_maybe_ignore_self_internal(
                i_s,
                name,
                options.super_count,
                false,
                |lookup_result, class, mro_index| {
                    let mut attr_kind = AttributeKind::Attribute;
                    let result = lookup_result.and_then(|inf| {
                        let mut bind_class_descriptors = |in_class, class_t, inf: Inferred| {
                            let i_s = i_s.with_class_context(&in_class);
                            let result = inf.bind_class_descriptors(
                                &i_s,
                                self,
                                in_class,
                                class_t,
                                options.add_issue,
                                options.apply_descriptors_origin,
                                options.as_type_type,
                            );
                            result.map(|inf| {
                                attr_kind = inf.1;
                                inf.0
                            })
                        };
                        match &class {
                            TypeOrClass::Class(in_class) => {
                                if class_infos.has_slots
                                    && options.apply_descriptors_origin.should_apply()
                                    && self.in_slots(i_s.db, name)
                                {
                                    (options.add_issue)(
                                        IssueKind::SlotsConflictWithClassVariableAccess {
                                            name: name.into(),
                                        },
                                    )
                                }
                                if let Some(as_type_type) =
                                    options.as_type_type.filter(|_| mro_index.0 == 0)
                                {
                                    let Type::Type(t) = as_type_type() else {
                                        unreachable!()
                                    };
                                    bind_class_descriptors(
                                        *in_class,
                                        &TypeOrClass::Type(Cow::Owned((*t).clone())),
                                        inf,
                                    )
                                } else {
                                    bind_class_descriptors(*in_class, &class, inf)
                                }
                            }
                            TypeOrClass::Type(t) => match t.as_ref() {
                                Type::Dataclass(d) => {
                                    bind_class_descriptors(d.class(i_s.db), &class, inf)
                                }
                                _ => Some(inf),
                            },
                        }
                    });
                    result.map(|lookup| {
                        if matches!(
                            attr_kind,
                            AttributeKind::Attribute | AttributeKind::AnnotatedAttribute
                        ) && options.apply_descriptors_origin.should_apply()
                        {
                            // It seems like normal class lookups are different for ClassVars and
                            // other attributes in Mypy, see testMetaclassConflictingInstanceVars
                            let metaclass_result = lookup_on_metaclass(true);
                            if metaclass_result.lookup.is_some()
                                && !metaclass_result.lookup.maybe_any(i_s.db).is_some()
                            {
                                return metaclass_result;
                            }
                        }
                        LookupDetails {
                            class,
                            lookup,
                            attr_kind,
                            mro_index: Some(mro_index),
                        }
                    })
                },
            )
        } else {
            None
        };
        if options.avoid_metaclass {
            return result.unwrap_or_else(LookupDetails::none);
        }
        match result {
            Some(LookupDetails {
                lookup: LookupResult::None,
                ..
            })
            | None => lookup_on_metaclass(false),
            Some(result) => result,
        }
    }

    pub fn generics(&self) -> Generics<'_> {
        if let Some(type_var_remap) = self.type_var_remap {
            Generics::List(type_var_remap, Some(&self.generics))
        } else {
            self.generics
        }
    }

    pub fn set_correct_generics_if_necessary_for_init_in_superclass(&mut self) {
        if self.type_var_remap.is_some() && matches!(self.generics, Generics::NotDefinedYet { .. })
        {
            self.generics = Generics::None;
        }
    }

    pub fn needs_generic_remapping_for_attributes(&self, i_s: &InferenceState, t: &Type) -> bool {
        !self.type_vars(i_s).is_empty() || t.has_self_type(i_s.db)
    }

    pub fn nth_type_argument(&self, db: &Database, nth: usize) -> Type {
        self.generics()
            .nth(db, nth)
            .expect_type_argument()
            .into_owned()
    }

    pub fn nth_param_spec_usage(
        &self,
        db: &'db Database,
        usage: &ParamSpecUsage,
    ) -> Cow<'_, ParamSpecArg> {
        let generic = self
            .generics()
            .nth_usage(db, &TypeVarLikeUsage::ParamSpec(usage.clone()));
        if let Generic::ParamSpecArg(p) = generic {
            p
        } else {
            unreachable!()
        }
    }

    pub fn mro_maybe_without_object(
        &self,
        db: &'db Database,
        without_object: bool,
    ) -> MroIterator<'db, 'a> {
        let class_infos = self.use_cached_class_infos(db);
        if let Some(type_var_remap) = self.type_var_remap
            && matches!(self.generics, Generics::Self_ { .. } | Generics::None)
        {
            return Class::new(
                self.node_ref,
                self.class_storage,
                Generics::List(type_var_remap, None),
                None,
            )
            .mro_maybe_without_object(db, without_object);
        }
        // TODO Do something similar for generics, because otherwise we lose type_var_remap
        MroIterator::new(
            db,
            TypeOrClass::Class(*self),
            self.generics,
            class_infos.mro.iter(),
            without_object || self.node_ref == db.python_state.object_node_ref(),
        )
    }

    pub fn mro(&self, db: &'db Database) -> MroIterator<'db, 'a> {
        self.mro_maybe_without_object(db, self.node_ref == db.python_state.object_node_ref())
    }

    pub fn bases(&self, db: &'a Database) -> impl Iterator<Item = TypeOrClass<'a>> {
        let generics = self.generics;
        self.use_cached_class_infos(db)
            .base_types()
            .map(move |b| apply_generics_to_base_class(db, b, generics))
    }
    pub fn class_in_mro(&self, db: &'db Database, node_ref: ClassNodeRef) -> Option<Class<'_>> {
        for (_, type_or_cls) in self.mro(db) {
            if let TypeOrClass::Class(c) = type_or_cls
                && c.node_ref == node_ref
            {
                return Some(c);
            }
        }
        None
    }

    pub fn is_object_class(&self, db: &Database) -> bool {
        self.node_ref == db.python_state.object_node_ref()
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut result = match format_data.style {
            FormatStyle::Short if !format_data.should_format_qualified(self.node_ref.as_link()) => {
                self.name().to_owned()
            }
            _ => self.qualified_name(format_data.db),
        };
        let type_var_likes = self.type_vars(&InferenceState::new(format_data.db, self.file));
        // Format classes that have not been initialized like Foo() or Foo[int] like "Foo".
        if !type_var_likes.is_empty()
            && !matches!(self.generics, Generics::NotDefinedYet { .. })
            && !type_var_likes.has_from_untyped_params()
        {
            // Returns something like [str] or [List[int], Set[Any]]
            let strings: Vec<_> = self
                .generics()
                .iter(format_data.db)
                .filter_map(|g| g.format(format_data))
                .collect();
            if strings.is_empty() {
                result += "[()]"
            } else {
                result += &format!("[{}]", strings.join(", "))
            };
        }

        if let Some(class_infos) = self.maybe_cached_class_infos(format_data.db) {
            match &class_infos.kind {
                ClassKind::NamedTuple => {
                    let named_tuple = self.maybe_named_tuple_base(format_data.db).unwrap();
                    return named_tuple.format_with_name(format_data, &result, self.generics);
                }
                ClassKind::Tuple if format_data.style == FormatStyle::MypyRevealType => {
                    for (_, type_or_class) in self.mro(format_data.db) {
                        if let TypeOrClass::Type(t) = type_or_class
                            && let Type::Tuple(tup) = t.as_ref()
                            && matches!(tup.args, TupleArgs::FixedLen(_) | TupleArgs::WithUnpack(_))
                        {
                            return tup.format_with_fallback(
                                format_data,
                                &format!(", fallback={result}"),
                            );
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
        Inferred::from_type(self.as_type_type(i_s.db))
    }

    pub fn generics_as_list(&self, db: &Database) -> ClassGenerics {
        // TODO we instantiate, because we cannot use use_cached_type_vars?
        let type_var_likes = self.type_vars(&InferenceState::new(db, self.file));
        match type_var_likes.is_empty() {
            false => match self.generics() {
                Generics::NotDefinedYet { .. } => ClassGenerics::List(GenericsList::new_generics(
                    type_var_likes
                        .iter()
                        .map(|t| t.as_default_or_any_generic_item(db))
                        .collect(),
                )),
                Generics::ExpressionWithClassType(file, expr) => {
                    ClassGenerics::ExpressionWithClassType(PointLink::new(
                        file.file_index,
                        expr.index(),
                    ))
                }
                Generics::SlicesWithClassTypes(file, slices) => {
                    ClassGenerics::SlicesWithClassTypes(PointLink::new(
                        file.file_index,
                        slices.index(),
                    ))
                }
                Generics::List(generics, None) => ClassGenerics::List((*generics).clone()),
                Generics::None => {
                    recoverable_error!("Generics::None should never appear with type vars");
                    ClassGenerics::List(GenericsList::new_generics(
                        type_var_likes
                            .iter()
                            .map(|t| t.as_default_or_any_generic_item(db))
                            .collect(),
                    ))
                }
                generics => ClassGenerics::List(GenericsList::new_generics(
                    generics.iter(db).map(|g| g.into_generic_item()).collect(),
                )),
            },
            true => ClassGenerics::new_none(),
        }
    }

    pub fn as_generic_class(&self, db: &Database) -> GenericClass {
        GenericClass {
            link: self.node_ref.as_link(),
            generics: self.generics_as_list(db),
        }
    }

    pub fn as_type(&self, db: &Database) -> Type {
        let class_infos = self.maybe_cached_class_infos(db);
        match class_infos.and_then(|c| c.undefined_generics_type.get().map(|t| t.as_ref())) {
            Some(Type::Dataclass(d)) => {
                Type::Dataclass(Dataclass::new(self.as_generic_class(db), d.options.clone()))
            }
            None | Some(Type::Class(_)) => Type::Class(self.as_generic_class(db)),
            Some(Type::TypedDict(td)) => Type::TypedDict(match &self.generics {
                Generics::List(list, None) => {
                    td.apply_generics(db, TypedDictGenerics::Generics((*list).clone()))
                }
                Generics::None => td.clone(),
                Generics::Self_ { class_ref } => {
                    let generics = class_ref
                        .use_cached_type_vars(db)
                        .as_default_or_any_generic_list(db);
                    td.apply_generics(db, TypedDictGenerics::Generics(generics))
                }
                _ => unreachable!("{:?}", self.generics),
            }),
            Some(t) => t.clone(),
        }
    }

    pub fn as_type_type(&self, db: &Database) -> Type {
        let class_infos = self.use_cached_class_infos(db);
        Type::Type(if matches!(self.generics, Generics::NotDefinedYet { .. }) {
            class_infos
                .undefined_generics_type
                .get_or_init(|| {
                    Arc::new(Type::new_class(
                        self.node_ref.as_link(),
                        ClassGenerics::NotDefinedYet,
                    ))
                })
                .clone()
        } else {
            Arc::new(self.as_type(db))
        })
    }

    pub fn find_relevant_constructor(
        &self,
        i_s: &InferenceState<'db, '_>,
        add_issue: &dyn Fn(IssueKind),
    ) -> ClassConstructor<'_> {
        if !i_s.db.mypy_compatible()
            && let MetaclassState::Some(metaclass) = self.use_cached_class_infos(i_s.db).metaclass
        {
            let meta = Class::from_undefined_generics(i_s.db, metaclass);
            let lookup = meta.instance().lookup(
                i_s,
                "__call__",
                InstanceLookupOptions::new(&|issue| {
                    debug!("TODO issue when resolving __call__ to find constructor {issue:?}");
                })
                .with_as_self_instance(&|| self.as_type_type(i_s.db)),
            );
            if let Some(inf) = lookup.lookup.maybe_inferred()
                && !lookup.class.is_bare_type(i_s.db)
            {
                let has_special_type =
                    inf.as_cow_type(i_s).for_all_in_union(i_s.db, &|t| match t {
                        Type::Callable(callable) => {
                            callable.return_type.for_all_in_union(i_s.db, &|t| match t {
                                Type::Class(class) => {
                                    class.link != self.node_ref.as_link()
                                        || match &callable.params {
                                            CallableParams::Simple(ps) => {
                                                // In case where *args is not involve, we assume
                                                // that the metaclass __call__ is  the initializer
                                                !ps.iter().any(|p| {
                                                    matches!(
                                                        p.type_,
                                                        ParamType::Star(
                                                            StarParamType::ArbitraryLen(Type::Any(
                                                                _
                                                            ))
                                                        )
                                                    )
                                                })
                                            }
                                            _ => false,
                                        }
                                }
                                Type::Any(_) => false,
                                _ => true,
                            })
                        }
                        _ => false,
                    });
                if has_special_type {
                    debug!(
                        "Found __call__ on metaclass {:?} with a special type \
                             and using it as a constructor for {:?}",
                        meta.qualified_name(i_s.db),
                        self.qualified_name(i_s.db)
                    );
                    return ClassConstructor::MetaclassDunderCall {
                        constructor: lookup.lookup,
                    };
                }
            }
        }
        let (__init__, init_class, init_mro_index) = self
            .lookup_and_class_and_maybe_ignore_self_internal(
                i_s,
                "__init__",
                0,
                self.is_protocol(i_s.db),
                |lookup, cls, mro_index| (lookup, cls, mro_index),
            );
        self.lookup_and_class_and_maybe_ignore_self_internal(
            i_s,
            "__new__",
            0,
            true,
            |__new__, cls, new_mro_index| {
                // This is just a weird heuristic Mypy uses, because the type system itself is very
                // unclear what to do if both __new__ and __init__ are present. So just only use
                // __new__ if it's in a lower MRO than an __init__.
                let mut is_new = new_mro_index < init_mro_index;
                if let Some(inf) = __new__.maybe_inferred()
                    && let Some(node_ref) = inf.maybe_saved_node_ref(i_s.db)
                    && let Some(func) = node_ref.maybe_function()
                    && let Some(return_annot) = func.return_annotation()
                {
                    let t = use_cached_return_annotation_type(i_s.db, node_ref.file, return_annot);
                    if !i_s.db.mypy_compatible()
                        && !cls
                            .maybe_class()
                            .is_some_and(|c| i_s.db.python_state.bare_type_node_ref() == c.node_ref)
                        && !matches!(
                            t.as_ref(),
                            Type::Self_ | Type::Any(AnyCause::Unannotated | AnyCause::FromError)
                        )
                    {
                        debug!(
                            "Use __new__ instead of __init__ because it has an explicit type {:?}",
                            t.format_short(i_s.db)
                        );
                        is_new = true;
                    }
                }
                if is_new && __new__.is_some() {
                    ClassConstructor::DunderNew {
                        // TODO this should not be bound
                        constructor: __new__
                            .and_then(|inf| {
                                Some(inf.bind_new_descriptors(
                                    i_s,
                                    self,
                                    cls.maybe_class(),
                                    add_issue,
                                ))
                            })
                            .unwrap(),
                    }
                } else {
                    ClassConstructor::DunderInit {
                        constructor: __init__,
                        init_class,
                    }
                }
            },
        )
    }

    pub(crate) fn execute(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> Inferred {
        if self.node_ref == i_s.db.python_state.dict_node_ref() {
            // This is a special case where we intercept the call to dict(..) when used with
            // TypedDict.
            if let Some(file) = args.in_file()
                && let Some(inf) = file
                    .inference(i_s)
                    .infer_dict_call_from_context(args, result_context)
            {
                return inf;
            }
        }
        match self.execute_and_return_generics(
            i_s,
            args,
            result_context,
            on_type_error,
            from_type_type,
        ) {
            ClassExecutionResult::ClassGenerics(mut generics) => {
                if generics.all_any_with_unknown_type_params()
                    && self.has_django_stubs_base_class(i_s.db)
                {
                    self.fill_django_default_generics(i_s, args, &mut generics);
                }
                let result = Inferred::from_type(Type::Class(GenericClass {
                    link: self.node_ref.as_link(),
                    generics,
                }));
                debug!("Class execute: {}", result.format_short(i_s));
                if self.node_ref == i_s.db.python_state.bare_type_node_ref()
                    && let Some(first_arg) =
                        args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)
                {
                    return execute_bare_type(i_s, first_arg);
                }
                result
            }
            ClassExecutionResult::Inferred(inf) => inf,
        }
    }

    fn fill_django_default_generics(
        &self,
        i_s: &InferenceState,
        args: &dyn Args,
        generics: &mut ClassGenerics,
    ) {
        let ClassGenerics::List(list) = generics else {
            recoverable_error!("Expected a list when trying to fill Django generics");
            return;
        };
        let mut known_type = None;
        if matches!(
            self.name(),
            "ForeignKey" | "OneToOneField" | "ManyToManyField"
        ) {
            known_type = args
                .iter(i_s.mode)
                .enumerate()
                .find_map(|(i, arg)| match &arg.kind {
                    ArgKind::Positional(arg) if i == 0 => {
                        Some(arg.infer(&mut ResultContext::Unknown))
                    }
                    ArgKind::Keyword(kwarg) if kwarg.key == "to" => {
                        Some(kwarg.infer(&mut ResultContext::Unknown))
                    }
                    _ => None,
                })
                .and_then(|inf| match inf.as_cow_type(i_s).as_ref() {
                    Type::Type(t) => Some(t.clone()),
                    Type::Literal(lit) => match lit.value(i_s.db) {
                        LiteralValue::String(name) => {
                            if let Type::Type(t) = args
                                .in_file()?
                                .lookup(
                                    i_s.db,
                                    |issue| {
                                        debug!(
                                            "Issue while looking up Django model \
                                            reference: {issue:?}"
                                        )
                                    },
                                    name,
                                )
                                .maybe_inferred()?
                                .as_cow_type(i_s)
                                .as_ref()
                            {
                                Some(t.clone())
                            } else {
                                None
                            }
                        }
                        _ => None,
                    },
                    _ => None,
                });
        }
        let nullable = args
            .iter(i_s.mode)
            .find_map(|arg| match &arg.kind {
                ArgKind::Keyword(kwarg) if kwarg.key == "null" => kwarg
                    .infer(&mut ResultContext::Unknown)
                    .maybe_bool_literal(i_s),
                _ => None,
            })
            .unwrap_or_default();
        let find_type = |name| {
            Some(GenericItem::TypeArg({
                let mut result = if let Some(known_type) = &known_type {
                    known_type.as_ref().clone()
                } else {
                    self.mro_maybe_without_object(i_s.db, true).find_map(
                        |(_, item)| match item {
                            TypeOrClass::Type(_) => None,
                            TypeOrClass::Class(class) => {
                                class.find_django_default_generic_inner(i_s.db, name)
                            }
                        },
                    )?
                };
                if nullable {
                    result.union_in_place(Type::None)
                }
                result
            }))
        };
        let entries = list
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                if let GenericItem::TypeArg(t) = entry
                    && matches!(t, Type::Any(AnyCause::UnknownTypeParam))
                {
                    if i == 0
                        && let Some(result) = find_type("_pyi_private_set_type")
                    {
                        return result;
                    } else if i == 1
                        && let Some(result) = find_type("_pyi_private_get_type")
                    {
                        return result;
                    }
                }
                entry.clone()
            })
            .collect();
        let lst = GenericsList::new_generics(entries);
        debug!(
            "Replaced {} generics with: [{}]",
            self.name(),
            lst.format(&FormatData::new_short(i_s.db)),
        );
        *generics = ClassGenerics::List(lst)
    }

    fn find_django_default_generic_inner(&self, db: &Database, name: &str) -> Option<Type> {
        let found = self.class_storage.class_symbol_table.lookup_symbol(name)?;
        let annotation = NodeRef::new(self.file, found)
            .expect_name()
            .maybe_annotated()?;
        let i_s = &InferenceState::new(db, self.file);
        let name_resolution = self.file.name_resolution_for_types(i_s);
        name_resolution.ensure_cached_annotation(annotation, false);
        Some(
            name_resolution
                .use_cached_annotation_type(annotation)
                .into_owned(),
        )
    }

    pub(crate) fn execute_and_return_generics(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
        from_type_type: bool,
    ) -> ClassExecutionResult {
        let class_infos = self.use_cached_class_infos(i_s.db);
        if !class_infos.abstract_attributes.is_empty()
            && !class_infos.incomplete_mro
            && matches!(self.generics, Generics::NotDefinedYet { .. })
        {
            args.add_issue(
                i_s,
                IssueKind::CannotInstantiateAbstractClass {
                    name: self.name().into(),
                    abstract_attributes: class_infos.abstract_attributes.clone(),
                },
            );
        }

        match &class_infos.kind {
            ClassKind::Enum if self.node_ref.as_link() != i_s.db.python_state.enum_auto_link() => {
                // For whatever reason, auto is special, because it is somehow defined as an enum as
                // well, which is very weird.

                if let Some(file) = args.in_file()
                    // Initializing enums without members is possible in Mypy and other type
                    // checkers, they can be used for example as a base class.
                    && !(self.file.file_index != i_s.db.python_state.enum_file().file_index
                        && args.iter(i_s.mode).count() == 1)
                {
                    return ClassExecutionResult::Inferred(
                        file.name_resolution_for_types(i_s)
                            .compute_functional_enum_definition(*self, args)
                            .unwrap_or_else(Inferred::new_invalid_type_definition),
                    );
                }
            }
            _ => (),
        }

        let d = |_: &dyn FuncLike, _: &Database| Some(format!("\"{}\"", self.name()));
        let on_type_error = on_type_error.with_custom_generate_diagnostic_string(&d);
        match self.find_relevant_constructor(i_s, &|issue| {
            args.add_issue(i_s, issue);
        }) {
            ClassConstructor::DunderNew { constructor } => {
                let result = constructor
                    .into_inferred()
                    .execute_with_details(i_s, args, result_context, on_type_error)
                    .as_type(i_s);
                // For Mypy only subclasses of the current class are valid, otherwise return the
                // current class. Diagnostics will care about these cases and raise errors when
                // needed.
                if !i_s.db.mypy_compatible()
                    || !result.is_any()
                        && Self::with_undefined_generics(self.node_ref)
                            .as_type(i_s.db)
                            .is_simple_super_type_of(i_s, &result)
                            .bool()
                {
                    ClassExecutionResult::Inferred(Inferred::from_type(result))
                } else if matches!(self.generics, Generics::NotDefinedYet { .. })
                    && !self.type_vars(i_s).is_empty()
                {
                    // This is a bit special, because in some cases like reversed() __new__ returns a
                    // super class of the current class. We use that super class to infer the generics
                    // that are relevant in the current class.
                    let mut matcher = Matcher::new_class_matcher(i_s, *self);
                    Self::with_self_generics(i_s.db, self.node_ref)
                        .as_type(i_s.db)
                        .is_sub_type_of(i_s, &mut matcher, &result);
                    ClassExecutionResult::ClassGenerics(
                        matcher
                            .into_type_arguments(i_s, self.node_ref.as_link(), true)
                            .type_arguments_into_class_generics(i_s.db),
                    )
                } else {
                    ClassExecutionResult::ClassGenerics(self.generics_as_list(i_s.db))
                }
            }
            ClassConstructor::DunderInit {
                constructor,
                init_class,
            } => {
                debug!("Check {} __init__", self.name());
                let _indent = debug_indent();
                self.type_check_dunder_init_func(
                    i_s,
                    constructor,
                    init_class,
                    args,
                    result_context,
                    on_type_error,
                    from_type_type,
                )
            }
            ClassConstructor::MetaclassDunderCall { constructor } => {
                ClassExecutionResult::Inferred(constructor.into_inferred().execute_with_details(
                    i_s,
                    args,
                    result_context,
                    on_type_error,
                ))
            }
        }
    }

    pub fn ensure_calculated_diagnostics_for_class(&self, db: &Database) -> Result<(), ()> {
        let class_block = self.node().block();
        if !self
            .node_ref
            .file
            .points
            .get(class_block.index())
            .calculated()
        {
            let result = self.file.ensure_module_symbols_flow_analysis(db);
            if result.is_err() {
                debug!(
                    "Wanted to calculate class {:?} diagnostics, but could not calculated file {}",
                    self.name(),
                    self.file.qualified_name(db)
                );
            }
            result?;
            let result = FLOW_ANALYSIS.with(|fa| {
                fa.with_new_empty_and_delay_further(db, || {
                    self.file
                        .inference(&InferenceState::from_class(db, self))
                        .calculate_class_block_diagnostics(*self, class_block)
                })
            });
            if result.is_err() {
                debug!(
                    "Wanted to calculate class {:?} diagnostics, but could not calculate file {}",
                    self.name(),
                    self.file.qualified_name(db)
                );
            }
            // At this point we just lose reachability information for the class. This is
            // probably the price we pay, since we allow weird (in reality impossible?) forward
            // statements in Mypy.
            result?
        }
        Ok(())
    }
    pub fn ensure_calculated_variance(&self, db: &Database) {
        let Some(class_infos) = self.maybe_cached_class_infos(db) else {
            debug!(
                "Avoid calculating variance, because the class infos are not ready. \
                    This is presumably because there are recursive type definitions"
            );
            return;
        };
        if class_infos.has_uncalculated_variances() {
            // It is very possible that the diagnostics are already calculating and the result will
            // error, but this does not matter, because we cannot guarantee that all variances are
            // calculated. This is a best effort thing.
            if class_infos.has_uncalculated_variances() {
                self.infer_variance_of_type_params(db, false);
            }
        }
    }

    pub fn infer_variance_for_index(
        &self,
        db: &Database,
        type_var_index: TypeVarIndex,
        check_narrowed: bool,
    ) -> Variance {
        let mut co = true;
        let mut contra = true;
        let file = self.node_ref.file;
        let i_s = &InferenceState::new(db, file);

        let in_definition = self.node_ref.as_link();

        // We intentionally don't use self.bases(db) here, because we want the bare type objects to
        // work with.
        let class_infos = self.use_cached_class_infos(db);
        let check_t = |base_t: &_| {
            check_type_var_variance_validity_for_type(i_s, in_definition, type_var_index, base_t)
        };
        for base_t in class_infos.base_types() {
            if let Some(co_contra) = check_t(base_t) {
                co &= co_contra.co;
                contra &= co_contra.contra;
                if !co && !contra {
                    return Variance::Invariant;
                }
            }
        }

        // Infer variance for members

        let instance = self.instance();
        let lookup_member = |name, node_index, is_self_attr| {
            let lookup = if check_narrowed || !file.points.get(node_index).needs_flow_analysis() {
                instance.lookup(
                    i_s,
                    name,
                    InstanceLookupOptions::new(&|issue| {
                        debug!(
                            "Issue while inferring variance on name {name}: {issue:?}. \
                            This should probably not be a problem."
                        );
                    })
                    // object has no generics and is therefore not relevant.
                    .without_object(),
                )
            } else {
                if is_self_attr {
                    if self
                        .class_storage
                        .class_symbol_table
                        .lookup_symbol(name)
                        .is_some()
                    {
                        debug!(
                            "Ignored the attribute because it was already checked while looking up class symbols"
                        );
                        return None;
                    }
                    // Check simple assignments like self.x = x. This solves most of the simple
                    // cases to improve variance inference.
                    let search_simple_name_assignments = || {
                        let n = Name::by_index(&file.tree, node_index);
                        let assignment = n.maybe_self_assignment_name_on_self_like()?;
                        let AssignmentContent::Normal(_, right_side) = assignment.unpack() else {
                            return None;
                        };
                        let expr = right_side.maybe_simple_expression()?;
                        let AtomContent::Name(assign_name) = expr.maybe_unpacked_atom()? else {
                            return None;
                        };
                        let p = file.points.get(assign_name.index());
                        if !p.calculated() || p.kind() != PointKind::Redirect {
                            return None;
                        }
                        let redirected_to = p.as_redirected_node_ref(db);
                        if redirected_to.point().needs_flow_analysis()
                            || redirected_to.file.file_index != file.file_index
                        {
                            return None;
                        }
                        if let Some(name) = redirected_to.maybe_name()
                            && let Some(name_def) = name.name_def()
                            && let Some(func) = name_def.maybe_parent_function_of_param()
                        {
                            let parent_scope =
                                FuncNodeRef::new(redirected_to.file, func.index()).parent_scope();
                            if !matches!(parent_scope, ParentScope::Class(c) if c == self.node_index)
                            {
                                return None;
                            }
                        }
                        Some(redirected_to.infer_name_of_definition_by_index(
                            &InferenceState::from_class(db, self),
                        ))
                    };
                    if let Some(inf) = search_simple_name_assignments() {
                        return Some((inf, AttributeKind::Attribute));
                    }
                }
                debug!(
                    "Ignored attribute {name} because we need to calculate the variance \
                        before the end of a module"
                );
                return None;
            };
            let mut attr_kind = lookup.attr_kind;
            let inf = lookup.lookup.into_inferred();
            match class_infos
                .undefined_generics_type
                .get()
                .map(|t| t.as_ref())
            {
                Some(Type::Dataclass(d)) => {
                    if let AttributeKind::AnnotatedAttribute = attr_kind
                        && d.options.frozen == Some(true)
                    {
                        attr_kind = AttributeKind::Property {
                            setter_type: None,
                            is_final: false,
                            is_abstract: true,
                        };
                    }
                }
                Some(Type::TypedDict(_)) => (), // TODO
                _ => (),
            }
            Some((inf, attr_kind))
        };
        for (table, is_self_table) in [
            (&self.class_storage.class_symbol_table, false),
            (&self.class_storage.self_symbol_table, true),
        ]
        .into_iter()
        {
            for (name, &node_index) in table.iter() {
                if ["__init__", "__new__", "__init_subclass__"].contains(&name) {
                    // Still needs to be calculated so the function is properly initialized for the
                    // `self.<name>` variables
                    NodeRef::new(self.file, node_index)
                        .infer_name_of_definition_by_index(&i_s.with_class_context(self));
                    continue;
                }
                if let Some((inf, attr_kind)) = lookup_member(name, node_index, is_self_table) {
                    // Mypy allows return types to be the current class.
                    let t = self.erase_return_self_type(inf.as_cow_type(i_s));
                    if let Some(co_contra) = check_t(&t) {
                        co &= co_contra.co;
                        contra &= co_contra.contra;
                        if !co_contra.contra {
                            contra = false;
                            // Attributes starting with _ are considered private and the variance
                            // of them are inferred as such.
                            let is_underscored = || name.starts_with('_') && !is_magic_method(name);
                            if attr_kind.is_writable() && !is_underscored() {
                                co = false;
                            }
                        }
                        if !co && !contra {
                            return Variance::Invariant;
                        }
                    }
                }
            }
        }
        match (co, contra) {
            (false, true) => Variance::Contravariant,
            (false, false) => unreachable!("Should have returned above"),
            _ => Variance::Covariant,
        }
    }

    fn erase_return_self_type<'t>(&self, t: Cow<'t, Type>) -> Cow<'t, Type> {
        let replace_callable = |c: &CallableContent| match &c.return_type {
            Type::Class(class) if class.link == self.node_ref.as_link() => {
                let mut new_c = c.clone();
                new_c.return_type = Type::Any(AnyCause::Internal);
                Some(Arc::new(new_c))
            }
            _ => None,
        };
        match t.as_ref() {
            Type::Callable(c) => {
                if let Some(c) = replace_callable(c) {
                    Cow::Owned(Type::Callable(c))
                } else {
                    t
                }
            }
            Type::FunctionOverload(o) => {
                let mut overloads = vec![];
                for (i, c) in o.iter_functions().enumerate() {
                    if let Some(new_c) = replace_callable(c) {
                        if overloads.is_empty() {
                            // We have to backfill
                            overloads.extend(o.iter_functions().take(i).cloned())
                        }
                        overloads.push(new_c)
                    } else if !overloads.is_empty() {
                        overloads.push(c.clone())
                    }
                }
                if overloads.is_empty() {
                    t
                } else {
                    Cow::Owned(Type::FunctionOverload(FunctionOverload::new(
                        overloads.into_boxed_slice(),
                    )))
                }
            }
            _ => t,
        }
    }

    pub(crate) fn simple_lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) -> LookupResult {
        self.lookup(i_s, name, ClassLookupOptions::new(&add_issue))
            .lookup
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
                        "__getitem__",
                        ClassLookupOptions::new(&|issue| {
                            slice_type.as_node_ref().add_issue(i_s, issue)
                        })
                        .with_kind(LookupKind::OnlyType),
                    )
                    .lookup
                    .into_maybe_inferred()
                {
                    return __getitem__.execute(i_s, &slice_type.as_args(*i_s));
                }
            }
            MetaclassState::Unknown => return Inferred::new_any_from_error(),
            MetaclassState::None => (),
        }
        slice_type
            .file
            .name_resolution_for_types(i_s)
            .compute_type_application_on_class(*self, *slice_type, result_context)
    }

    pub fn in_slots(&self, db: &Database, name: &str) -> bool {
        for (_, type_or_class) in self.mro_maybe_without_object(db, true) {
            match type_or_class {
                TypeOrClass::Type(_) => (),
                TypeOrClass::Class(class) => {
                    if let Some(slots) = &class.class_storage.slots
                        && slots.iter().any(|slot| {
                            let s = slot.as_str(db);
                            s == name
                        })
                    {
                        return true;
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
                    if let Some(dataclass) = class.maybe_dataclass(i_s.db)
                        && dataclass.options.slots
                    {
                        if Dataclass::has_slot(i_s.db, &dataclass, name) {
                            return;
                        }
                    } else {
                        let Some(slots) = &class.class_storage.slots else {
                            return;
                        };
                        if slots.iter().any(|slot| {
                            let s = slot.as_str(i_s.db);
                            s == name || s == "__dict__"
                        }) {
                            return;
                        }
                    }
                    if let Some(on_class) = class.lookup_symbol(i_s, name).into_maybe_inferred()
                        && on_class
                            .as_cow_type(&i_s.with_class_context(&class))
                            .is_func_or_overload()
                    {
                        // Adds IssueType::CannotAssignToAMethod in other places.
                        return;
                    }
                    if class.lookup_symbol(i_s, "__setattr__").is_some() {
                        return;
                    }
                }
            }
        }
        add_issue(IssueKind::AssigningToNameOutsideOfSlots {
            name: name.into(),
            class: self.qualified_name(i_s.db).into(),
        })
    }

    pub(crate) fn check_self_definition(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) {
        self.lookup_and_class_and_maybe_ignore_self_internal(
            i_s,
            name,
            0,
            false,
            |lookup, c, _| {
                if let Some(inf) = lookup.into_maybe_inferred() {
                    if inf.maybe_saved_specific(i_s.db)
                        == Some(Specific::AnnotationOrTypeCommentClassVar)
                        && !c.is_protocol(i_s.db)
                    {
                        add_issue(IssueKind::CannotAssignToClassVarViaInstance {
                            name: name.into(),
                        })
                    } else if inf.as_cow_type(i_s).is_func_or_overload_not_any_callable() {
                        // See testSlotsAssignmentWithMethodReassign
                        //add_issue(IssueType::CannotAssignToAMethod);
                    }
                }
            },
        );
        self.check_slots(i_s, add_issue, name)
    }

    pub fn maybe_named_tuple_base(&self, db: &'a Database) -> Option<Arc<NamedTuple>> {
        if self.use_cached_class_infos(db).kind == ClassKind::NamedTuple {
            for (_, base) in self.mro(db) {
                if let TypeOrClass::Type(base) = base
                    && let Type::NamedTuple(named_tuple) = base.as_ref()
                {
                    return Some(named_tuple.clone());
                }
            }
            unreachable!()
        }
        None
    }

    pub fn maybe_tuple_base(&self, db: &Database) -> Option<Arc<Tuple>> {
        match self.use_cached_class_infos(db).kind {
            ClassKind::NamedTuple | ClassKind::Tuple => {
                for (_, base) in self.mro(db) {
                    if let TypeOrClass::Type(base) = base {
                        return Some(match base.as_ref() {
                            Type::NamedTuple(named_tuple) => named_tuple.as_tuple(),
                            Type::Tuple(tup) => tup.clone(),
                            _ => continue,
                        });
                    }
                }
                unreachable!()
            }
            _ => None,
        }
    }

    pub fn maybe_dataclass(&self, db: &Database) -> Option<Arc<Dataclass>> {
        // TODO this should probably not be needed.
        match self
            .maybe_cached_class_infos(db)?
            .undefined_generics_type
            .get()?
            .as_ref()
        {
            Type::Dataclass(d) => Some(d.clone()),
            _ => None,
        }
    }

    pub fn maybe_enum(&self, db: &Database) -> Option<Arc<Enum>> {
        match self
            .maybe_cached_class_infos(db)?
            .undefined_generics_type
            .get()?
            .as_ref()
        {
            Type::Enum(e) => Some(e.clone()),
            _ => None,
        }
    }

    pub fn maybe_typed_dict(&self) -> Option<Arc<TypedDict>> {
        self.maybe_typed_dict_definition()
            .map(|tdd| tdd.typed_dict())
    }

    pub fn has_customized_enum_new(&self, i_s: &InferenceState) -> bool {
        for (_, c) in self.mro_maybe_without_object(i_s.db, true) {
            let (c, lookup) = c.lookup_symbol(i_s, "__new__");
            if lookup.into_maybe_inferred().is_some() {
                let Some(class) = c else { unreachable!() };
                return class.node_ref.file.file_index
                    != i_s.db.python_state.enum_file().file_index;
            }
        }
        false
    }

    pub fn is_dict_with_str_any(&self, db: &Database) -> bool {
        if self.node_ref != db.python_state.dict_node_ref() {
            return false;
        }
        self.nth_type_argument(db, 0) == db.python_state.str_type()
            && self.nth_type_argument(db, 1).is_any()
    }

    pub fn has_django_stubs_base_class(&self, db: &Database) -> bool {
        *self
            .use_cached_class_infos(db)
            .in_django_stubs
            .get_or_init(|| {
                self.node_ref.file.is_from_django(db)
                    || self.bases(db).any(|b| match b {
                        TypeOrClass::Type(_) => false,
                        TypeOrClass::Class(class) => class.has_django_stubs_base_class(db),
                    })
            })
    }

    fn is_django_field(&self, db: &Database) -> bool {
        self.has_django_stubs_base_class(db)
            && self.mro_maybe_without_object(db, true).any(|(_, base)| {
                base.maybe_class().is_some_and(|cls| {
                    cls.has_django_stubs_base_class(db)
                        && cls.name() == "Field"
                        && cls.file.name(db) == "fields"
                })
            })
    }
}

impl fmt::Debug for Class<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Class")
            .field("file_index", &self.node_ref.file.file_index)
            .field("node_index", &self.node_ref.node_index)
            .field("name", &self.name())
            .field("generics", &self.generics)
            .field("type_var_remap", &self.type_var_remap)
            .finish()
    }
}

pub(crate) fn check_type_var_variance_validity_for_type(
    i_s: &InferenceState,
    in_definition: PointLink,
    type_var_index: TypeVarIndex,
    base_t: &Type,
) -> Option<CoContra> {
    let with_object_t = base_t.replace_type_var_likes(i_s.db, &mut |usage| {
        if usage.index() == type_var_index
            && usage.in_definition() == in_definition
            && let TypeVarLikeUsage::TypeVar(_) = usage
        {
            Some(GenericItem::TypeArg(i_s.db.python_state.object_type()))
        } else {
            None
        }
    })?;
    Some(CoContra {
        co: base_t.is_simple_sub_type_of(i_s, &with_object_t).bool(),
        contra: with_object_t.is_simple_sub_type_of(i_s, base_t).bool(),
    })
}

pub(crate) struct CoContra {
    pub co: bool,
    pub contra: bool,
}

pub(crate) enum ClassExecutionResult {
    ClassGenerics(ClassGenerics),
    Inferred(Inferred),
}

pub(crate) struct MroIterator<'db, 'a> {
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
pub(crate) enum TypeOrClass<'a> {
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
                _ => unreachable!(),
            },
        }
    }

    pub fn qualified_name(&self, db: &'a Database) -> String {
        match self {
            Self::Class(class) => class.qualified_name(db),
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.class(db).qualified_name(db),
                Type::NamedTuple(nt) => nt.qualified_name(db),
                _ => self.name(db).into(),
            },
        }
    }

    #[inline]
    pub fn maybe_class(&self) -> Option<Class<'a>> {
        match self {
            TypeOrClass::Class(c) => Some(*c),
            TypeOrClass::Type(_) => None,
        }
    }

    pub fn as_base_class<'x>(&'x self, db: &'x Database, cls: &Class<'x>) -> Option<Class<'x>> {
        match self {
            TypeOrClass::Class(c) => Some(*c),
            TypeOrClass::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => Some(d.as_base_class(db, cls.generics)),
                _ => None,
            },
        }
    }

    pub fn is_object(&self, db: &Database) -> bool {
        matches!(self, TypeOrClass::Class(c) if c.node_ref == db.python_state.object_node_ref())
    }

    pub fn is_bare_type(&self, db: &Database) -> bool {
        matches!(self, TypeOrClass::Class(c) if c.node_ref == db.python_state.bare_type_node_ref())
    }

    pub fn is_frozen_dataclass(&self) -> bool {
        match self {
            Self::Type(t) => match t.as_ref() {
                Type::Dataclass(d) => d.options.frozen == Some(true),
                _ => false,
            },
            Self::Class(_) => false,
        }
    }
    pub fn originates_in_builtins_or_typing(&self, db: &Database) -> bool {
        match self {
            TypeOrClass::Class(c) => {
                let class_file_index = c.node_ref.file_index();
                class_file_index == db.python_state.builtins().file_index
                    || c.node_ref.file_index() == db.python_state.typing().file_index
            }
            TypeOrClass::Type(_) => true,
        }
    }

    pub fn as_type(&self, db: &Database) -> Type {
        match self {
            TypeOrClass::Class(c) => c.as_type(db),
            TypeOrClass::Type(t) => t.clone().into_owned(),
        }
    }

    pub fn is_protocol(&self, db: &Database) -> bool {
        match self {
            TypeOrClass::Class(c) => c.is_protocol(db),
            TypeOrClass::Type(_) => false,
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
        Type::Class(c) => {
            TypeOrClass::Class(match &c.generics {
                ClassGenerics::List(g) => {
                    if matches!(generics, Generics::Self_ { .. }) {
                        // Self generics imply that there is no remapping of generics necessary. We can
                        // therefore simply use the class in the mro.
                        c.class(db)
                    } else {
                        Class::from_position(ClassNodeRef::from_link(db, c.link), generics, Some(g))
                    }
                }
                ClassGenerics::None { .. } => {
                    Class::from_position(ClassNodeRef::from_link(db, c.link), generics, None)
                }
                _ => unreachable!(
                    "{}",
                    NodeRef::from_link(db, c.link)
                        .maybe_class()
                        .unwrap()
                        .name()
                        .as_code()
                ),
            })
        }
        // TODO is this needed?
        //Type::RecursiveType(r) if matches!(r.origin(db), RecursiveTypeOrigin::Class(_)) => TypeOrClass::Class(Class::from_position(NodeRef::from_link(db, r.link), generics, r.generics.as_ref())),
        _ if matches!(generics, Generics::None | Generics::NotDefinedYet { .. }) => {
            TypeOrClass::Type(Cow::Borrowed(t))
        }
        _ => {
            let new_t = t.replace_type_var_likes_and_self(
                db,
                &mut |usage| Some(generics.nth_usage(db, &usage).into_generic_item()),
                &|| None,
            );
            TypeOrClass::Type(new_t.map(Cow::Owned).unwrap_or_else(|| Cow::Borrowed(t)))
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
        _ => {
            let ErrorStrs { got, expected } = format_got_expected(i_s.db, t2, t1);
            notes.push(format!(r#"    {name}: expected "{expected}", got "{got}""#).into())
        }
    }
}

fn protocol_conflict_note(db: &Database, other: &Type) -> Box<str> {
    match other {
        Type::Module(file_index) => format!(
            "Following member(s) of Module \"{}\" have conflicts:",
            db.loaded_python_file(*file_index).qualified_name(db)
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
        CallableLike::Callable(c) => notes.push(format_callable(c).into()),
        CallableLike::Overload(o) => {
            for c in o.iter_functions() {
                notes.push(format!("{prefix}@overload").into());
                notes.push(format_callable(c).into());
            }
        }
    }
}

fn init_as_callable(
    i_s: &InferenceState,
    cls: Class,
    inf: Inferred,
    init_class: TypeOrClass,
) -> Option<CallableLike> {
    let mut init_class = init_class;
    let class_infos = cls.use_cached_class_infos(i_s.db);
    if let MetaclassState::Some(_) = class_infos.metaclass {
        let meta = class_infos.metaclass(i_s.db);
        if meta.has_django_stubs_base_class(i_s.db) && meta.name() == "ModelBase" {
            let c = CallableContent::new_non_generic(
                i_s.db,
                Some(DbString::StringSlice(cls.name_string_slice())),
                None,
                cls.node_ref.as_link(),
                django_model_params(i_s, cls),
                cls.as_type(i_s.db),
            );
            return Some(CallableLike::Callable(Arc::new(c)));
        }
    }
    let cls = if matches!(cls.generics(), Generics::NotDefinedYet { .. }) {
        if let TypeOrClass::Class(init_class) = &mut init_class {
            // Make sure generics are not Any
            init_class.generics = Generics::Self_ {
                class_ref: cls.node_ref,
            };
        }
        Class::with_self_generics(i_s.db, cls.node_ref)
    } else {
        cls
    };
    let init_class = init_class.maybe_class();
    let callable = if let Some(c) = init_class {
        let i_s = &i_s.with_class_context(&c);
        inf.as_cow_type(i_s).maybe_callable(i_s)?
    } else {
        inf.as_cow_type(i_s).maybe_callable(i_s)?
    };
    let to_callable = |original: &CallableContent| {
        // Since __init__ does not have a return, we need to check the params
        // of the __init__ functions and the class as a return type separately.
        original.remove_first_positional_param().map(|mut c| {
            let self_ = if c.kind.had_first_self_or_class_annotation()
                && let Some(first) = original.first_positional_type()
            {
                first
            } else {
                cls.as_type(i_s.db)
            };
            let needs_type_var_remap = init_class
                .is_some_and(|c| !c.type_vars(i_s).is_empty() && c.node_ref != cls.node_ref);

            // If the __init__ comes from a super class, we need to fetch the generics that
            // are relevant for our class.
            if c.has_self_type(i_s.db) || needs_type_var_remap {
                c = c.replace_type_var_likes_and_self_inplace(
                    i_s.db,
                    &mut |usage| {
                        if needs_type_var_remap
                            && let Some(func_class) = init_class
                            && let Some(result) = maybe_class_usage(i_s.db, &func_class, &usage)
                        {
                            return Some(result);
                        }
                        None
                    },
                    &|| Some(self_.clone()),
                )
            }
            c.return_type = self_;

            // Now we have two sets of generics, the generics for the class and the
            // generics for the __init__ function. We merge those and then set the proper
            // ids for the type vars.
            let class_type_vars = cls.type_vars(i_s);
            let mut tv_vec = class_type_vars.as_vec();
            tv_vec.extend(c.type_vars.iter().cloned());
            c.type_vars = TypeVarLikes::from_vec(tv_vec);
            let c_defined_at = c.defined_at;
            if !c.type_vars.is_empty() {
                c = c.replace_type_var_likes_and_self_inplace(
                    i_s.db,
                    &mut |mut usage| {
                        let in_def = usage.in_definition();
                        if cls.node_ref.as_link() == in_def {
                            usage.update_in_definition_and_index(c_defined_at, usage.index());
                        } else if c_defined_at == in_def {
                            usage.update_in_definition_and_index(
                                c_defined_at,
                                (class_type_vars.len() + usage.index().as_usize()).into(),
                            )
                        } else {
                            return None;
                        }
                        Some(usage.into_generic_item())
                    },
                    &|| None,
                );
            }
            Arc::new(c)
        })
    };
    Some(match callable {
        CallableLike::Callable(c) => CallableLike::Callable(to_callable(&c)?),
        CallableLike::Overload(callables) => {
            let funcs: Box<_> = callables
                .iter_functions()
                .filter_map(|c| to_callable(c))
                .collect();
            match funcs.len() {
                0 => return None,
                1 => CallableLike::Callable(funcs.into_vec().into_iter().next().unwrap()),
                _ => CallableLike::Overload(FunctionOverload::new(funcs)),
            }
        }
    })
}

fn django_model_params(i_s: &InferenceState, cls: Class) -> Vec<CallableParam> {
    let mut params = vec![];
    for (_, cls) in cls.mro(i_s.db) {
        if let Some(cls) = cls.maybe_class() {
            for (_, symbol) in cls.class_storage.class_symbol_table.iter() {
                let name_ref = NodeRef::new(cls.file, *symbol);
                let name = name_ref.expect_name();
                if name.maybe_assignment_definition_name().is_none() {
                    // Currently we only check assignments, this is a performance optimization. We
                    // don't make a type out of every function.
                    continue;
                }
                let name_def_ref = name_ref.name_def_ref_of_name();
                if let Some(inf) = name_def_ref.maybe_inferred(i_s)
                    && let Some(field_cls) = inf.as_cow_type(i_s).maybe_class(i_s.db)
                    && field_cls.is_django_field(i_s.db)
                {
                    params.push(CallableParam {
                        name: Some(DbString::StringSlice(StringSlice::from_name(
                            cls.file.file_index,
                            name,
                        ))),
                        // TODO this should not be any but probably the generic of
                        // _pyi_private_get_type
                        type_: ParamType::PositionalOrKeyword(Type::Any(AnyCause::Internal)),
                        // Params are optional in Django.
                        has_default: true,
                        might_have_type_vars: false,
                    });
                }
            }
        }
    }
    // Since some Django users set fields in very dynamic ways we don't want to ensure type safety
    // here yet.
    add_any_params_to_params(&mut params);
    params
}

pub(crate) enum ClassConstructor<'a> {
    // A data structure to show wheter __init__ or __new__ is the relevant constructor for a class
    DunderNew {
        constructor: LookupResult,
    },
    DunderInit {
        constructor: LookupResult,
        init_class: TypeOrClass<'a>,
    },
    MetaclassDunderCall {
        constructor: LookupResult,
    },
}

impl ClassConstructor<'_> {
    pub fn maybe_callable(self, i_s: &InferenceState, cls: Class) -> Option<CallableLike> {
        match self {
            Self::DunderNew { constructor } | Self::MetaclassDunderCall { constructor } => {
                constructor
                    .into_inferred()
                    .as_cow_type(i_s)
                    .maybe_callable(i_s)
            }
            Self::DunderInit {
                constructor,
                init_class,
            } => init_as_callable(i_s, cls, constructor.into_inferred(), init_class),
        }
    }

    fn into_type(self, i_s: &InferenceState, cls: Class) -> Option<Type> {
        self.maybe_callable(i_s, cls).map(|c| c.into())
    }
}

pub(crate) struct ClassLookupOptions<'x> {
    add_issue: &'x dyn Fn(IssueKind),
    kind: LookupKind,
    apply_descriptors_origin: ApplyClassDescriptorsOrigin,
    super_count: usize,
    avoid_metaclass: bool,
    as_type_type: Option<&'x dyn Fn() -> Type>,
}

impl<'x> ClassLookupOptions<'x> {
    pub(crate) fn new(add_issue: &'x dyn Fn(IssueKind)) -> Self {
        Self {
            add_issue,
            kind: LookupKind::Normal,
            apply_descriptors_origin: ApplyClassDescriptorsOrigin::ClassAccess,
            super_count: 0,
            avoid_metaclass: false,
            as_type_type: None,
        }
    }

    pub fn with_ignore_self(mut self) -> Self {
        self.super_count = 1;
        self
    }

    pub fn with_as_type_type(mut self, as_type_type: &'x dyn Fn() -> Type) -> Self {
        self.as_type_type = Some(as_type_type);
        self
    }

    pub fn with_origin(mut self, apply_descriptors_origin: ApplyClassDescriptorsOrigin) -> Self {
        self.apply_descriptors_origin = apply_descriptors_origin;
        self
    }

    pub fn with_kind(mut self, kind: LookupKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn with_super_count(mut self, super_count: usize) -> Self {
        self.super_count = super_count;
        self
    }

    pub fn with_avoid_metaclass(mut self) -> Self {
        self.avoid_metaclass = true;
        self
    }
}

fn execute_bare_type(i_s: &InferenceState<'_, '_>, first_arg: Inferred) -> Inferred {
    let mut type_part = Type::Never(NeverCause::Other);
    for t in first_arg.as_cow_type(i_s).iter_with_unpacked_unions(i_s.db) {
        type_part.union_in_place(match t {
            Type::Class(_)
            | Type::None
            | Type::Any(_)
            | Type::Self_
            | Type::Dataclass(_)
            | Type::Tuple(_)
            | Type::NewType(_)
            | Type::TypeVar(_)
            | Type::Enum(_) => t.clone(),
            Type::Literal(l) => l.fallback_type(i_s.db),
            Type::Type(type_) => match type_.as_ref() {
                Type::Class(c) => match &c.class(i_s.db).use_cached_class_infos(i_s.db).metaclass {
                    MetaclassState::Some(link) => Type::new_class(*link, ClassGenerics::new_none()),
                    _ => i_s.db.python_state.object_type().clone(),
                },
                Type::Any(cause) => Type::Any(*cause),
                _ => i_s.db.python_state.object_type(),
            },
            Type::Module(_) | Type::NamedTuple(_) => i_s.db.python_state.module_type(),
            Type::EnumMember(m) => Type::Enum(m.enum_.clone()),
            Type::Super { .. } => i_s.db.python_state.super_type(),
            Type::ParamSpecArgs(_) => i_s.db.python_state.tuple_of_obj.clone(),
            Type::TypedDict(_) | Type::ParamSpecKwargs(_) => {
                i_s.db.python_state.dict_of_str_and_obj.clone()
            }
            // We cannot simply use type[object] here, because the type is unclear for narrowing at
            // this point.
            // We should provide better types here if possible for other types. This is however
            // pretty hard for callables for example, because they have different types depending
            // on the definition (e.g. builtins vs. normal Python functions) and we don't have that
            // information available.
            _ => Type::ERROR,
        })
    }
    if type_part.is_never() {
        first_arg // Must be never
    } else {
        Inferred::from_type(Type::Type(Arc::new(type_part)))
    }
}
