use std::{
    cell::{Cell, RefCell},
    sync::Arc,
};

use parsa_python_cst::TypeLike;

use crate::{
    file::FLOW_ANALYSIS,
    inferred::AttributeKind,
    match_::MismatchReason,
    prelude::*,
    type_::{ErrorStrs, LookupArgs, LookupKind, PrettyCallableOptions, format_got_expected},
    type_helpers::{ClassLookupOptions, Instance, InstanceLookupOptions, TypeOrClass},
    utils::is_magic_method,
};

impl<'db: 'a, 'a> Class<'a> {
    pub fn check_protocol_match(
        &self,
        i_s: &InferenceState<'db, '_>,
        matcher: &mut Matcher,
        other: &Type,
    ) -> Match {
        if other.is_calculating(i_s.db) {
            // Recursive types might not be ready yet while calculating the classes, see also
            // no_crash_with_recursive_named_tuple
            debug!(
                "Abort protocol matching against calculating recursive type, returning Match::false"
            );
            return Match::new_false();
        }
        // Since protocols can cause access of narrowing information, we should make sure that
        // there is no narrowing information from potentially other files. Also the frames might be
        // borrowed, so avoid that scenario.
        FLOW_ANALYSIS.with_new_empty_and_delay_further(i_s.db, || {
            self.check_protocol_match_part2(i_s, matcher, other)
        })
    }
    fn check_protocol_match_part2(
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
        let mut match_result = Match::new_true();
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
                                    false
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

                let initial_binding_error = Cell::new(false);
                let instance = self.instance();
                // In general Self must be changed to the "other" provided, but there are sometimes
                // issues with self: <X> types that don't map cleanly onto the "other". So we
                // simply choose to not map Self in these cases for now. Ideally this would be
                // handled deeper, but I'm not sure that's easy.
                let mut protocol_lookup_details = instance.lookup(
                    i_s,
                    name,
                    InstanceLookupOptions::new(&|issue| {
                        initial_binding_error.set(true);
                        debug!("Binding error when matching protocol: {issue:?}");
                        false
                    })
                    .with_as_self_instance(&|| other.clone())
                    .with_avoid_inferring_return_types()
                    .with_disallow_lazy_bound_method(),
                );
                let had_binding_error = Cell::new(false);
                if initial_binding_error.get() {
                    protocol_lookup_details = instance.lookup(
                        i_s,
                        name,
                        InstanceLookupOptions::new(&|issue| {
                            had_binding_error.set(true);
                            debug!("Repeated binding error when matching protocol: {issue:?}");
                            false
                        })
                        .with_avoid_inferring_return_types()
                        .with_disallow_lazy_bound_method(),
                    );
                }
                let protocol_inf = protocol_lookup_details.lookup.into_inferred();

                // It's a bit weird that we have to filter out TypeVarLikes here, but at the moment
                // there is no way to have that information when we gather Protocol members.
                if matches!(
                    protocol_inf.maybe_complex_point(i_s.db),
                    Some(ComplexPoint::TypeVarLike(_))
                ) {
                    continue;
                }

                let mut had_lookup_error = false;
                // Magic methods are probably never relevant on the object, since Python
                // ignores all self attributes. This is especially the case if Enums classes
                // are passed. However it feels a bit weird here and might need to be changed
                // in the future.
                let kind = if is_magic_method(name) {
                    LookupKind::OnlyType
                } else {
                    LookupKind::Normal
                };
                other.run_after_lookup_on_each_union_member(
                    None,
                    LookupArgs::new(i_s, self.node_ref.file, name).with_kind(kind)
                    .with_add_issue(
                    &|issue| {
                        // Deprecated should not affect matching
                        if let IssueKind::Deprecated { .. } = &issue {
                            return false;
                        }
                        let issue_str = self.node_ref.issue_to_str(i_s, issue);
                        debug!("Issue in protocol: {}", issue_str);
                        *had_error.borrow_mut() = Some(issue_str);
                        false
                    }),
                    &mut ResultContext::Unknown,
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
                                            &self.lookup(i_s, name, ClassLookupOptions::new(&|_| false)
                                                    .with_as_type_type(&|| if other.is_subclassable(i_s.db) {
                                                        Type::Type(Arc::new(other.clone()))
                                                    } else {
                                                        self.as_type_type(i_s.db)
                                                    })
                                                )
                                                .lookup
                                                .into_inferred()
                                                .as_cow_type(i_s),
                                            &cls.simple_lookup(i_s, |_| false, name)
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
                                                        cls.find_relevant_constructor(i_s, &|_| false)
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
                            match_result &= m;

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
            match_result
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
                let name_node_ref = NodeRef::new(c.node_ref.file, protocol_member.name_index);
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
    if let (
        Type::Callable(_) | Type::FunctionOverload(_),
        Type::Callable(_) | Type::FunctionOverload(_) | Type::Type(_),
    ) = (full1, full2)
    {
        notes.push("    Expected:".into());
        if let Some(c1) = full1.maybe_callable(i_s)
            && let Some(c2) = full2.maybe_callable(i_s)
        {
            format_callable_like(i_s.db, notes, &c1, &c2);
            notes.push("    Got:".into());
            format_callable_like(i_s.db, notes, &c2, &c1);
            return;
        }
    }
    let ErrorStrs { got, expected } = format_got_expected(i_s.db, t2, t1);
    notes.push(format!(r#"    {name}: expected "{expected}", got "{got}""#).into())
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
                PrettyCallableOptions {
                    show_self_annotation: other_had_first_annotation,
                    avoid_classmethod_param: true,
                    ..Default::default()
                }
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
