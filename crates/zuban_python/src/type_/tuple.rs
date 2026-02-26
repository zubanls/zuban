use std::{
    hash::{Hash, Hasher},
    ops::Deref,
    sync::{
        Arc, OnceLock,
        atomic::{AtomicBool, Ordering},
    },
};

use num_bigint::BigInt;

use super::{
    ClassGenerics, CustomBehavior, FormatStyle, GenericItem, GenericsList, LookupResult,
    RecursiveType, TypeVarLikeUsage, TypeVarTupleUsage, utils::method_with_fallback,
};
use crate::{
    arguments::Args,
    database::Database,
    debug,
    diagnostics::IssueKind,
    format_data::FormatData,
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{Generics, IteratorContent, OnTypeError},
    recoverable_error,
    result_context::ResultContext,
    type_::{AnyCause, Type},
    type_helpers::{Class, ClassExecutionResult, Instance, LookupDetails, TypeOrClass},
    utils::{arc_slice_into_vec, join_with_commas},
};

thread_local! {
    static ARBITRARY_TUPLE: Arc<Tuple> = Tuple::new_arbitrary_length(Type::Any(AnyCause::Todo));
    static ARBITRARY_TUPLE_ARGS_FROM_ERROR: TupleArgs = TupleArgs::ArbitraryLen(Arc::new(Type::ERROR));
    static ARBITRARY_TUPLE_FROM_ERROR: Arc<Tuple> = Tuple::new_arbitrary_length(Type::ERROR);
}

#[derive(Debug)]
pub(crate) struct Tuple {
    pub args: TupleArgs,
    currently_calculating_generics: AtomicBool,
    pub(super) tuple_class_generics: OnceLock<GenericsList>,
}

impl Clone for Tuple {
    fn clone(&self) -> Self {
        Tuple {
            args: self.args.clone(),
            currently_calculating_generics: AtomicBool::new(false),
            tuple_class_generics: self.tuple_class_generics.clone(),
        }
    }
}

impl Tuple {
    pub fn new(args: TupleArgs) -> Arc<Self> {
        Arc::new(Self {
            args,
            currently_calculating_generics: AtomicBool::new(false),
            tuple_class_generics: OnceLock::new(),
        })
    }

    pub fn new_arbitrary_length_with_class_generics(t: Type, generics: GenericsList) -> Arc<Self> {
        Arc::new(Self {
            args: TupleArgs::ArbitraryLen(Arc::new(t)),
            currently_calculating_generics: AtomicBool::new(false),
            tuple_class_generics: OnceLock::from(generics),
        })
    }

    pub fn new_fixed_length(args: Arc<[Type]>) -> Arc<Self> {
        Self::new(TupleArgs::FixedLen(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Arc<Self> {
        Self::new(TupleArgs::ArbitraryLen(Arc::new(arg)))
    }

    pub fn new_arbitrary_length_with_any() -> Arc<Self> {
        ARBITRARY_TUPLE.with(|t| t.clone())
    }

    pub fn new_arbitrary_length_with_any_from_error() -> Arc<Self> {
        ARBITRARY_TUPLE_FROM_ERROR.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        debug_assert!(!self.currently_calculating_generics.load(Ordering::Relaxed));
        self.tuple_class_generics.get_or_init(|| {
            self.currently_calculating_generics
                .store(true, Ordering::Relaxed);
            let t = self
                .args
                .simplified_union_of_tuple_entries(&InferenceState::new_in_unknown_file(db))
                .avoid_implicit_literal(db);
            debug!("Calculated tuple class generics: {}", t.format_short(db));
            self.currently_calculating_generics
                .store(false, Ordering::Relaxed);
            GenericsList::new_generics(Arc::new([GenericItem::TypeArg(t)]))
        })
    }

    pub fn is_calculating(&self) -> bool {
        self.currently_calculating_generics.load(Ordering::Relaxed)
    }

    pub fn fallback_type(&self, db: &Database) -> &Type {
        let GenericItem::TypeArg(t) = self.tuple_class_generics(db).nth(0.into()).unwrap() else {
            unreachable!();
        };
        t
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.format_with_fallback(format_data, "")
    }

    pub fn format_with_fallback(&self, format_data: &FormatData, fallback: &str) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::MypyRevealType => "builtins.tuple",
        };
        format!("{base}[{}{fallback}]", self.args.format(format_data)).into()
    }

    pub fn iter(&self) -> IteratorContent {
        match &self.args {
            TupleArgs::FixedLen(ts) => IteratorContent::new_tuple(ts.clone()),
            TupleArgs::ArbitraryLen(t) => {
                IteratorContent::Inferred(Inferred::from_type(t.as_ref().clone()))
            }
            TupleArgs::WithUnpack(w) => IteratorContent::WithUnpack {
                unpack: w.clone(),
                before_index: 0,
                after_index: 0,
            },
        }
    }

    pub fn format_with_simplified_unpack(&self, format_data: &FormatData) -> Box<str> {
        match &self.args {
            TupleArgs::WithUnpack(w) if w.before.is_empty() && w.after.is_empty() => w
                .unpack
                .format(format_data)
                .unwrap_or("Unpack[Never]".into()),
            _ => format!("Unpack[{}]", self.format(format_data)).into(),
        }
    }

    pub(crate) fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Inferred {
        // Make sure the get_item part is inferred.
        slice_type.infer(i_s);
        const ZERO: BigInt = BigInt::ZERO;
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => {
                let index_inf = simple
                    .file
                    .inference(i_s)
                    .infer_expression(simple.named_expr.expression());
                if !index_inf
                    .as_cow_type(i_s)
                    .is_simple_sub_type_of(i_s, &i_s.db.python_state.int_type())
                    .bool()
                {
                    Instance::new(self.class(i_s.db), None)
                        .type_lookup(i_s, add_issue, "__getitem__")
                        .into_inferred()
                        .execute(i_s, &slice_type.as_args(*i_s));
                    return Inferred::new_any(AnyCause::Todo);
                }
                match &self.args {
                    TupleArgs::ArbitraryLen(t) => Inferred::from_type(t.as_ref().clone()),
                    _ => {
                        let out_of_range = |variadic_max_len| {
                            add_issue(IssueKind::TupleIndexOutOfRange { variadic_max_len });
                            Some(Inferred::new_any_from_error())
                        };
                        index_inf
                            .run_on_int_literals(i_s, |index| match &self.args {
                                TupleArgs::FixedLen(ts) => {
                                    let index: usize = if *index < ZERO {
                                        let index = ts.len() as isize + index;
                                        match index.try_into() {
                                            Ok(index) => index,
                                            Err(_) => return out_of_range(None),
                                        }
                                    } else {
                                        match index.try_into() {
                                            Ok(index) => index,
                                            Err(_) => return out_of_range(None),
                                        }
                                    };
                                    if let Some(t) = ts.as_ref().get(index) {
                                        Some(Inferred::from_type(t.clone()))
                                    } else {
                                        out_of_range(None)
                                    }
                                }
                                TupleArgs::WithUnpack(with_unpack) => {
                                    if *index < ZERO {
                                        let after_len = with_unpack.after.len();
                                        let max_len = after_len + with_unpack.before.len();
                                        let Ok(index) = usize::try_from(-index - 1) else {
                                            return out_of_range(Some(max_len));
                                        };
                                        Some(Inferred::from_type(if index >= max_len {
                                            return out_of_range(Some(max_len));
                                        } else if index < after_len {
                                            with_unpack.after[after_len - index - 1].clone()
                                        } else {
                                            match &with_unpack.unpack {
                                                TupleUnpack::TypeVarTuple(_) => {
                                                    i_s.db.python_state.object_type()
                                                }
                                                TupleUnpack::ArbitraryLen(t) => {
                                                    Type::simplified_union_from_iterators(
                                                        i_s,
                                                        with_unpack
                                                            .before
                                                            .iter()
                                                            .rev()
                                                            .take(index - after_len + 1)
                                                            .rev()
                                                            .chain(std::iter::once(t)),
                                                    )
                                                }
                                            }
                                        }))
                                    } else {
                                        let before_len = with_unpack.before.len();
                                        let max_len = before_len + with_unpack.after.len();
                                        let Ok(index) = usize::try_from(index) else {
                                            return out_of_range(Some(max_len));
                                        };
                                        Some(Inferred::from_type(if index >= max_len {
                                            return out_of_range(Some(max_len));
                                        } else if index < before_len {
                                            with_unpack.before[index].clone()
                                        } else {
                                            match &with_unpack.unpack {
                                                TupleUnpack::TypeVarTuple(_) => {
                                                    i_s.db.python_state.object_type()
                                                }
                                                TupleUnpack::ArbitraryLen(t) => {
                                                    Type::simplified_union_from_iterators(
                                                        i_s,
                                                        std::iter::once(t).chain(
                                                            with_unpack
                                                                .after
                                                                .iter()
                                                                .take(index - before_len + 1),
                                                        ),
                                                    )
                                                }
                                            }
                                        }))
                                    }
                                }
                                TupleArgs::ArbitraryLen(_) => unreachable!(),
                            })
                            .unwrap_or_else(|| {
                                Inferred::from_type(
                                    self.args.simplified_union_of_tuple_entries(i_s),
                                )
                            })
                    }
                }
            }
            SliceTypeContent::Slices(_) | SliceTypeContent::Starred(_) => i_s
                .db
                .python_state
                .bare_tuple_type_with_any()
                .get_item(i_s, None, slice_type, result_context),
            SliceTypeContent::Slice(slice) => slice
                .callback_on_tuple_indexes(i_s, |start, end, step| {
                    if *step == ZERO {
                        add_issue(IssueKind::TupleSliceStepCannotBeZero);
                        return Inferred::from_type(Type::Tuple(
                            Self::new_arbitrary_length_with_any_from_error(),
                        ));
                    }
                    let as_fixed_len_tuple = |ts: &[Type]| {
                        Inferred::from_type(Type::Tuple(Tuple::new_fixed_length({
                            let len = ts.len() as isize;
                            let remove_negative = |i: Option<&BigInt>| {
                                Some({
                                    match i? {
                                        i if *i < ZERO => i + len,
                                        i => i.clone(),
                                    }
                                })
                            };
                            let as_skip = |i: Option<BigInt>| match i {
                                Some(i) => i.max(ZERO).try_into().unwrap_or(usize::MAX),
                                None => 0,
                            };
                            let start = remove_negative(start);
                            let end = remove_negative(end);
                            let (skip_left, skip_right) = if *step < ZERO {
                                (end.map(|e| e + 1), start.map(|s| len - s - 1))
                            } else {
                                (start, end.map(|e| len - e))
                            };
                            let iter = ts
                                .iter()
                                .skip(as_skip(skip_left))
                                .rev()
                                .skip(as_skip(skip_right));
                            // Stepping by usize::MAX is good enough if it's bigger than that
                            if *step < ZERO {
                                iter.step_by((-step).try_into().unwrap_or(usize::MAX))
                                    .cloned()
                                    .collect()
                            } else {
                                iter.rev()
                                    .step_by(step.try_into().unwrap_or(usize::MAX))
                                    .cloned()
                                    .collect()
                            }
                        })))
                    };
                    match &self.args {
                        TupleArgs::FixedLen(ts) => as_fixed_len_tuple(ts),
                        TupleArgs::WithUnpack(with_unpack) => {
                            let ambiguous = || {
                                add_issue(IssueKind::AmbigousSliceOfVariadicTuple);
                                Inferred::from_type(Type::Tuple(
                                    Self::new_arbitrary_length_with_any_from_error(),
                                ))
                            };
                            // These are special cases where we know that the resulting tuple
                            // is just part of the prefix or suffix and therefore results in a
                            // normal fixed length tuple that can have an arbitrary step.
                            let is_same_sign = start
                                .zip(end)
                                .map(|(s, e)| *s < ZERO && *e < ZERO || *s >= ZERO && *e >= ZERO)
                                .unwrap_or(true);
                            if is_same_sign {
                                let before_len = with_unpack.before.len().into();
                                let after_len = with_unpack.after.len().into();
                                if let Some(end) = end {
                                    if *step < ZERO {
                                        if *end < ZERO && -end - 1 <= after_len {
                                            return as_fixed_len_tuple(&with_unpack.after);
                                        }
                                    } else if *end >= ZERO && *end <= before_len {
                                        return as_fixed_len_tuple(&with_unpack.before);
                                    }
                                }
                                if let Some(start) = start {
                                    if *step < ZERO {
                                        if *start >= ZERO && *start <= before_len {
                                            return as_fixed_len_tuple(&with_unpack.before);
                                        }
                                    } else if *start < ZERO && -start <= after_len {
                                        return as_fixed_len_tuple(&with_unpack.after);
                                    }
                                }
                            }

                            let zero = ZERO;
                            // These are the normal cases where we skip an or at the start/end.
                            let out = if *step == 1.into() {
                                let skip_start = start.unwrap_or(&zero);
                                if *skip_start < ZERO || end.is_some_and(|e| *e >= ZERO) {
                                    return ambiguous();
                                }
                                let skip_end = -end.unwrap_or(&ZERO);

                                if *skip_start > with_unpack.before.len().into()
                                    || skip_end > with_unpack.after.len().into()
                                {
                                    return ambiguous();
                                }
                                // unwrap: A tuple should never exceed usize
                                let skip_start = skip_start.try_into().unwrap();
                                let skip_end = skip_end.try_into().unwrap();
                                WithUnpack {
                                    before: with_unpack
                                        .before
                                        .iter()
                                        .skip(skip_start)
                                        .cloned()
                                        .collect(),
                                    unpack: with_unpack.unpack.clone(),
                                    after: with_unpack
                                        .after
                                        .iter()
                                        .rev()
                                        .skip(skip_end)
                                        .rev()
                                        .cloned()
                                        .collect(),
                                }
                            } else if *step == (-1).into() {
                                let skip_start = end.unwrap_or(&zero);
                                if *skip_start < ZERO || start.is_some_and(|s| *s >= ZERO) {
                                    return ambiguous();
                                }
                                let skip_end = -start.unwrap_or(&ZERO);

                                if *skip_start > with_unpack.before.len().into()
                                    || skip_end > with_unpack.after.len().into()
                                {
                                    return ambiguous();
                                }
                                // unwrap: A tuple should never exceed usize
                                let skip_start = skip_start.try_into().unwrap();
                                let skip_end = skip_end.try_into().unwrap();
                                WithUnpack {
                                    before: with_unpack
                                        .after
                                        .iter()
                                        .rev()
                                        .skip(skip_end)
                                        .cloned()
                                        .collect(),
                                    unpack: with_unpack.unpack.clone(),
                                    after: with_unpack
                                        .before
                                        .iter()
                                        .skip(skip_start)
                                        .rev()
                                        .cloned()
                                        .collect(),
                                }
                            } else {
                                return ambiguous();
                            };
                            if out.before.is_empty()
                                && out.after.is_empty()
                                && let TupleUnpack::ArbitraryLen(t) = out.unpack
                            {
                                // We can simplify
                                return Inferred::from_type(Type::Tuple(Tuple::new(
                                    TupleArgs::ArbitraryLen(Arc::new(t)),
                                )));
                            }
                            Inferred::from_type(Type::Tuple(Tuple::new(TupleArgs::WithUnpack(out))))
                        }
                        TupleArgs::ArbitraryLen(_) => {
                            Inferred::from_type(Type::Tuple(Arc::new(self.clone())))
                        }
                    }
                })
                .unwrap_or_else(|| {
                    Inferred::from_type(Type::Tuple(Tuple::new_arbitrary_length(
                        self.args.simplified_union_of_tuple_entries(i_s),
                    )))
                }),
        }
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match &self.args {
            TupleArgs::FixedLen(ts) => ts.iter().any(|t| t.find_in_type(db, check)),
            TupleArgs::ArbitraryLen(t) => t.find_in_type(db, check),
            TupleArgs::WithUnpack(with_unpack) => with_unpack.find_in_type(db, check),
        }
    }

    pub fn class<'db: 'a, 'a>(&'a self, db: &'db Database) -> Class<'a> {
        let generics = self.tuple_class_generics(db);
        Class::from_position(
            db.python_state.tuple_node_ref(),
            Generics::List(generics, None),
            None,
        )
    }
}

impl PartialEq for Tuple {
    fn eq(&self, other: &Self) -> bool {
        self.args == other.args
    }
}

impl Eq for Tuple {}

impl Hash for Tuple {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.args.hash(state);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TupleUnpack {
    TypeVarTuple(TypeVarTupleUsage),
    ArbitraryLen(Type),
}

impl TupleUnpack {
    pub fn is_any(&self) -> bool {
        matches!(self, Self::ArbitraryLen(Type::Any(_)))
    }

    pub fn fallback_bound(&self, db: &Database) -> Type {
        match self {
            TupleUnpack::TypeVarTuple(_) => db.python_state.object_type(),
            TupleUnpack::ArbitraryLen(t) => t.clone(),
        }
    }

    fn format(&self, format_data: &FormatData) -> Option<Box<str>> {
        match self {
            Self::TypeVarTuple(t) => format_data.format_type_var_tuple(t),
            Self::ArbitraryLen(t) => {
                Some(format!("Unpack[Tuple[{}, ...]]", t.format(format_data)).into())
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct WithUnpack {
    pub before: Arc<[Type]>,
    pub unpack: TupleUnpack,
    pub after: Arc<[Type]>,
}

impl WithUnpack {
    pub fn with_empty_before_and_after(unpack: TupleUnpack) -> Self {
        Self {
            before: Arc::from([]),
            unpack,
            after: Arc::from([]),
        }
    }

    fn format(&self, format_data: &FormatData) -> Box<str> {
        join_with_commas(
            self.before
                .iter()
                .map(|t| t.format(format_data))
                .chain(self.unpack.format(format_data))
                .chain(self.after.iter().map(|t| t.format(format_data))),
        )
        .into()
    }

    pub fn find_in_type(&self, db: &Database, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.before.iter().any(|t| t.find_in_type(db, check))
            || match &self.unpack {
                TupleUnpack::TypeVarTuple(_) => false,
                TupleUnpack::ArbitraryLen(t) => t.find_in_type(db, check),
            }
            || self.before.iter().any(|t| t.find_in_type(db, check))
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Arc<RecursiveType>>,
    ) -> bool {
        self.before
            .iter()
            .any(|t| t.has_any_internal(i_s, already_checked))
            || match &self.unpack {
                TupleUnpack::TypeVarTuple(_) => false,
                TupleUnpack::ArbitraryLen(t) => t.has_any_internal(i_s, already_checked),
            }
            || self
                .after
                .iter()
                .any(|t| t.has_any_internal(i_s, already_checked))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TupleArgs {
    WithUnpack(WithUnpack),
    FixedLen(Arc<[Type]>),
    ArbitraryLen(Arc<Type>),
}

impl TupleArgs {
    pub fn new_arbitrary_from_error() -> Self {
        ARBITRARY_TUPLE_ARGS_FROM_ERROR.with(|t| t.clone())
    }

    pub fn maybe_any(&self) -> Option<AnyCause> {
        match self {
            Self::ArbitraryLen(t) => match t.as_ref() {
                Type::Any(cause) => Some(*cause),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        self.has_any_internal(i_s, &mut Vec::new())
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, TupleArgs::FixedLen(fixed) if fixed.is_empty())
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Arc<RecursiveType>>,
    ) -> bool {
        match self {
            Self::FixedLen(ts) => ts.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::ArbitraryLen(t) => t.has_any_internal(i_s, already_checked),
            Self::WithUnpack(with_unpack) => with_unpack.has_any_internal(i_s, already_checked),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::FixedLen(ts) if ts.is_empty() => Box::from("()"),
            Self::FixedLen(ts) => join_with_commas(ts.iter().map(|g| g.format(format_data))).into(),
            Self::ArbitraryLen(t) => format!("{}, ...", t.format(format_data)).into(),
            Self::WithUnpack(unpack) => unpack.format(format_data),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage) + ?Sized>(&self, found_type_var: &mut C) {
        match self {
            TupleArgs::FixedLen(ts) => {
                for t in ts.iter() {
                    t.search_type_vars(found_type_var)
                }
            }
            TupleArgs::ArbitraryLen(t) => t.search_type_vars(found_type_var),
            TupleArgs::WithUnpack(with_unpack) => {
                for t in with_unpack.before.iter() {
                    t.search_type_vars(found_type_var)
                }
                match &with_unpack.unpack {
                    TupleUnpack::TypeVarTuple(tvt) => {
                        found_type_var(TypeVarLikeUsage::TypeVarTuple(tvt.clone()))
                    }
                    TupleUnpack::ArbitraryLen(t) => t.search_type_vars(found_type_var),
                }
                for t in with_unpack.after.iter() {
                    t.search_type_vars(found_type_var)
                }
            }
        }
    }

    pub fn merge_matching_parts(&self, db: &Database, other: &Self) -> Self {
        use TupleArgs::*;
        match (self, other) {
            (FixedLen(ts1), FixedLen(ts2)) if ts1.len() == ts2.len() => {
                Self::FixedLen(
                    // Performance issue: Same as above
                    ts1.iter()
                        .zip(ts2.iter())
                        .map(|(t1, t2)| t1.merge_matching_parts(db, t2))
                        .collect(),
                )
            }
            (ArbitraryLen(t1), ArbitraryLen(t2)) => {
                Self::ArbitraryLen(Arc::new(t1.merge_matching_parts(db, t2)))
            }
            _ => Tuple::new_arbitrary_length_with_any().args.clone(),
        }
    }

    pub fn add_before_and_after(
        self,
        before: impl MergableTypes,
        after: impl MergableTypes,
    ) -> Self {
        match self {
            TupleArgs::FixedLen(fixed) => TupleArgs::FixedLen({
                before
                    .into_iter_types()
                    .chain(fixed.iter().cloned())
                    .chain(after.into_iter_types())
                    .collect()
            }),
            TupleArgs::WithUnpack(new) => TupleArgs::WithUnpack(WithUnpack {
                before: merge_types(before, new.before),
                unpack: new.unpack,
                // TODO this after is wrong
                after: merge_types(after, new.after),
            }),
            TupleArgs::ArbitraryLen(t) => {
                if before.len() == 0 && after.is_empty() {
                    TupleArgs::ArbitraryLen(t)
                } else {
                    TupleArgs::WithUnpack(WithUnpack {
                        before: before.into(),
                        unpack: TupleUnpack::ArbitraryLen(Arc::unwrap_or_clone(t)),
                        after: after.into(),
                    })
                }
            }
        }
    }

    pub fn simplified_union_of_tuple_entries(&self, i_s: &InferenceState) -> Type {
        // We avoid implicit literals, because it would otherwise be very slow to calculate the
        // generics of a tuple with entries 1-1000 (exponential blowup).
        match self {
            TupleArgs::FixedLen(ts) => Type::simplified_union_from_iterators(
                i_s,
                ts.iter().map(|t| t.avoid_implicit_literal_cow(i_s.db)),
            ),
            TupleArgs::WithUnpack(with_unpack) => match &with_unpack.unpack {
                TupleUnpack::TypeVarTuple(_) => i_s.db.python_state.object_type(),
                TupleUnpack::ArbitraryLen(t) => Type::simplified_union_from_iterators(
                    i_s,
                    with_unpack
                        .before
                        .iter()
                        .chain(std::iter::once(t))
                        .chain(with_unpack.after.iter())
                        .map(|t| t.avoid_implicit_literal_cow(i_s.db)),
                ),
            },
            TupleArgs::ArbitraryLen(t) => (**t).clone(),
        }
    }
}

pub trait MergableTypes: Deref<Target = [Type]> + Into<Arc<[Type]>> {
    fn into_iter_types(self) -> impl Iterator<Item = Type>;
    fn into_types_vec(self) -> Vec<Type>;
}

impl MergableTypes for Vec<Type> {
    fn into_iter_types(self) -> impl Iterator<Item = Type> {
        self.into_iter()
    }

    fn into_types_vec(self) -> Vec<Type> {
        self
    }
}

impl MergableTypes for Arc<[Type]> {
    fn into_iter_types(self) -> impl Iterator<Item = Type> {
        self.into_types_vec().into_iter()
    }

    fn into_types_vec(self) -> Vec<Type> {
        arc_slice_into_vec(self)
    }
}

fn merge_types(original: impl MergableTypes, new: impl MergableTypes) -> Arc<[Type]> {
    if original.is_empty() {
        new.into()
    } else if new.is_empty() {
        original.into()
    } else {
        let mut original: Vec<_> = original.into_types_vec();
        original.extend(new.into_iter_types());
        original.into()
    }
}

pub(crate) fn lookup_on_tuple<'x>(
    tuple: &'x Arc<Tuple>,
    i_s: &'x InferenceState,
    add_issue: impl Fn(IssueKind) -> bool,
    name: &str,
) -> LookupDetails<'x> {
    lookup_tuple_magic_methods(tuple.clone(), name).or_else(|| {
        let tuple_cls = tuple.class(i_s.db);
        for (mro_index, class_or_type) in tuple_cls.mro(i_s.db) {
            let (cls, lookup) = class_or_type.lookup_symbol(i_s, name);
            if let Some(inf) = lookup.into_maybe_inferred() {
                let Some(cls) = cls else {
                    unreachable!();
                };
                let Some((lookup, attr_kind)) = inf.bind_instance_descriptors(
                    i_s,
                    name,
                    tuple_cls.as_type(i_s.db),
                    cls,
                    add_issue,
                    mro_index,
                    false,
                    false,
                ) else {
                    return LookupDetails::none();
                };
                return LookupDetails {
                    class: class_or_type,
                    lookup: LookupResult::UnknownName(lookup),
                    attr_kind,
                    mro_index: None,
                };
            }
        }
        debug!("TODO tuple object lookups");
        LookupDetails::new(
            Type::Tuple(tuple.clone()),
            LookupResult::None,
            AttributeKind::Attribute,
        )
    })
}

pub fn lookup_tuple_magic_methods(tuple: Arc<Tuple>, name: &str) -> LookupDetails<'static> {
    LookupDetails::new(
        Type::Tuple(tuple.clone()),
        match name {
            "__mul__" | "__rmul__" => {
                LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(
                    CustomBehavior::new_method(tuple_mul, Some(Arc::new(Type::Tuple(tuple)))),
                )))
            }
            "__add__" => LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(
                CustomBehavior::new_method(tuple_add, Some(Arc::new(Type::Tuple(tuple)))),
            ))),
            _ => LookupResult::None,
        },
        AttributeKind::DefMethod { is_final: false },
    )
}

fn tuple_add<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::Tuple(tuple) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        tuple.clone(),
        "__add__",
        tuple_add_internal,
        || Instance::new(tuple.class(i_s.db), None),
    )
}

fn tuple_add_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple1: Arc<Tuple>,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    for (_, type_or_class) in first.as_cow_type(i_s).mro(i_s.db) {
        let TypeOrClass::Type(t) = type_or_class else {
            continue;
        };
        let Type::Tuple(tuple2) = t.as_ref() else {
            continue;
        };
        return Some(Inferred::from_type(Type::Tuple(Tuple::new(
            match (&tuple1.args, &tuple2.args) {
                (TupleArgs::FixedLen(ts1), TupleArgs::FixedLen(ts2)) => {
                    TupleArgs::FixedLen(ts1.iter().chain(ts2.iter()).cloned().collect())
                }
                (TupleArgs::FixedLen(ts1), TupleArgs::WithUnpack(u)) => {
                    TupleArgs::WithUnpack(WithUnpack {
                        before: ts1.iter().chain(u.before.iter()).cloned().collect(),
                        unpack: u.unpack.clone(),
                        after: u.after.clone(),
                    })
                }
                (TupleArgs::WithUnpack(u), TupleArgs::FixedLen(ts2)) => {
                    TupleArgs::WithUnpack(WithUnpack {
                        before: u.before.clone(),
                        unpack: u.unpack.clone(),
                        after: u.after.iter().chain(ts2.iter()).cloned().collect(),
                    })
                }
                _ => return None,
            },
        ))));
    }
    None
}
fn tuple_mul<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
    bound: Option<&Type>,
) -> Inferred {
    let Type::Tuple(tuple) = bound.unwrap() else {
        unreachable!();
    };
    method_with_fallback(
        i_s,
        args,
        result_context,
        on_type_error,
        tuple.clone(),
        "__mul__",
        tuple_mul_internal,
        || Instance::new(tuple.class(i_s.db), None),
    )
}

fn tuple_mul_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple: Arc<Tuple>,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    match &tuple.args {
        TupleArgs::FixedLen(ts) => first.run_on_int_literals(i_s, |int| {
            let zero = BigInt::ZERO;
            let int = int.max(&zero);
            if *int > 10.into() {
                debug!("TODO Do we really want extremely large tuples?");
                return None;
            }
            let int: usize = int.try_into().unwrap();
            Some(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                ts.iter().cycle().take(int * ts.len()).cloned().collect(),
            ))))
        }),
        TupleArgs::ArbitraryLen(_) => Some(Inferred::from_type(Type::Tuple(tuple))),
        TupleArgs::WithUnpack(_) => {
            debug!("TODO How do we multiply with unpack tuples?");
            None
        }
    }
}

pub fn execute_tuple_class<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError,
) -> Inferred {
    let tup_cls = i_s
        .db
        .python_state
        .tuple_class_with_generics_to_be_defined();
    let context_t = result_context.with_type_if_exists_and_replace_type_var_likes(i_s, |t| {
        t.iter_with_unpacked_unions(i_s.db)
            .map(|t| match t {
                Type::Tuple(tup) => tup.class(i_s.db).as_type(i_s.db),
                _ => t.clone(),
            })
            .collect()
    });
    let mut new_result_context = match &context_t {
        Some(t) => ResultContext::new_known(t),
        None => ResultContext::ValueExpected,
    };
    let class_execution_result = tup_cls.execute_and_return_generics(
        i_s,
        args,
        &mut new_result_context,
        on_type_error,
        true,
    );
    // While we theoretically now have a result, but that result is essentially just an instance of
    // "class tuple". We however would want a Tuple[int, ...] instead. Therefore we unpack the type
    // we got here.
    let ClassExecutionResult::Inferred(inf) = class_execution_result else {
        recoverable_error!("Expected a __new__ within builtins.tuple");
        return Inferred::new_any_from_error();
    };
    match inf.as_cow_type(i_s).as_ref() {
        Type::Class(tup_cls) => {
            let ClassGenerics::List(generics_list) = &tup_cls.generics else {
                recoverable_error!("Expected a tuple with one type argument in typeshed");
                return Inferred::new_any_from_error();
            };
            let Some(GenericItem::TypeArg(t)) = generics_list.iter().next() else {
                recoverable_error!("Expected a tuple with one type argument in typeshed");
                return Inferred::new_any_from_error();
            };
            Inferred::from_type(Type::Tuple(
                Tuple::new_arbitrary_length_with_class_generics(t.clone(), generics_list.clone()),
            ))
        }
        _ => {
            recoverable_error!("Expected tuple.__new__ to return the tuple class");
            return Inferred::new_any_from_error();
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct MaybeUnpackGatherer {
    before: Vec<Type>,
    unpack: Option<TupleUnpack>,
    after: Vec<Type>,
}

impl MaybeUnpackGatherer {
    pub fn add_type(&mut self, t: Type) {
        if self.unpack.is_none() {
            self.before.push(t)
        } else {
            self.after.push(t)
        }
    }

    pub fn add_types(&mut self, types: impl Iterator<Item = Type>) {
        if self.unpack.is_none() {
            self.before.extend(types);
        } else {
            self.after.extend(types);
        }
    }

    pub fn add_tuple_args(&mut self, tup: &TupleArgs) -> Result<(), TupleUnpack> {
        match tup {
            TupleArgs::FixedLen(ts) => {
                self.add_types(ts.iter().cloned());
                Ok(())
            }
            TupleArgs::ArbitraryLen(t) => {
                self.add_unpack(TupleUnpack::ArbitraryLen(t.as_ref().clone()))
            }
            TupleArgs::WithUnpack(w) => self.add_with_unpack(w.clone()),
        }
    }

    pub fn add_unpack(&mut self, unpack: TupleUnpack) -> Result<(), TupleUnpack> {
        if self.unpack.is_some() {
            Err(unpack)
        } else {
            self.unpack = Some(unpack);
            Ok(())
        }
    }

    pub fn add_with_unpack(&mut self, u: WithUnpack) -> Result<(), TupleUnpack> {
        if self.unpack.is_some() {
            return Err(u.unpack);
        }
        self.before.extend(u.before.iter().cloned());
        self.unpack = Some(u.unpack);
        self.after.extend(u.after.iter().cloned());
        Ok(())
    }

    pub fn into_tuple_args(self) -> TupleArgs {
        match self.unpack {
            Some(unpack) => match unpack {
                TupleUnpack::ArbitraryLen(t) if self.before.is_empty() && self.after.is_empty() => {
                    TupleArgs::ArbitraryLen(Arc::new(t))
                }
                _ => TupleArgs::WithUnpack(WithUnpack {
                    before: self.before.into(),
                    unpack,
                    after: self.after.into(),
                }),
            },
            None => {
                debug_assert!(self.after.is_empty());
                TupleArgs::FixedLen(self.before.into())
            }
        }
    }
}
