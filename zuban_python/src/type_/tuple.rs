use std::{cell::OnceCell, rc::Rc};

use super::{
    common_base_type, simplified_union_from_iterators, utils::method_with_fallback, CustomBehavior,
    FormatStyle, GenericItem, GenericsList, RecursiveType, TypeVarLikeUsage, TypeVarTupleUsage,
};
use crate::{
    arguments::Args,
    database::Database,
    debug,
    diagnostics::IssueType,
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{
        FormatData, IteratorContent, LookupKind, LookupResult, OnTypeError, ParamsStyle,
        ResultContext,
    },
    node_ref::NodeRef,
    type_::{AnyCause, Type},
    type_helpers::{Instance, LookupDetails, TypeOrClass},
    utils::{join_with_commas, rc_slice_into_vec},
};

thread_local! {
    static ARBITRARY_TUPLE: Rc<Tuple> = Tuple::new_arbitrary_length(Type::Any(AnyCause::Todo));
    static ARBITRARY_TUPLE_FROM_ERROR: Rc<Tuple> = Tuple::new_arbitrary_length(Type::Any(AnyCause::FromError));
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tuple {
    pub args: TupleArgs,
    pub(super) tuple_class_generics: OnceCell<GenericsList>,
}

impl Tuple {
    pub fn new(args: TupleArgs) -> Rc<Self> {
        Rc::new(Self {
            args,
            tuple_class_generics: OnceCell::new(),
        })
    }

    pub fn new_fixed_length(args: Rc<[Type]>) -> Rc<Self> {
        Self::new(TupleArgs::FixedLen(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Rc<Self> {
        Self::new(TupleArgs::ArbitraryLen(Box::new(arg)))
    }

    pub fn new_arbitrary_length_with_any() -> Rc<Self> {
        ARBITRARY_TUPLE.with(|t| t.clone())
    }

    pub fn new_arbitrary_length_with_any_from_error() -> Rc<Self> {
        ARBITRARY_TUPLE_FROM_ERROR.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        self.tuple_class_generics.get_or_init(|| {
            GenericsList::new_generics(Rc::new([GenericItem::TypeArg(
                self.args
                    .common_base_for_all_items(&InferenceState::new(db)),
            )]))
        })
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.format_with_fallback(format_data, "")
    }

    pub fn format_with_fallback(&self, format_data: &FormatData, fallback: &str) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
        };
        format!("{base}[{}{fallback}]", self.args.format(format_data)).into()
    }

    pub fn iter(&self, i_s: &InferenceState, from: NodeRef) -> IteratorContent {
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
            TupleArgs::WithUnpack(w) if w.before.is_empty() && w.after.is_empty() => {
                w.unpack.format(format_data)
            }
            _ => self.format(format_data),
        }
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        // Make sure the get_item part is inferred.
        slice_type.infer(i_s);
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
                    Instance::new(i_s.db.python_state.tuple_class(i_s.db, self), None)
                        .lookup(
                            i_s,
                            |issue| slice_type.as_node_ref().add_issue(i_s, issue),
                            "__getitem__",
                            LookupKind::OnlyType,
                        )
                        .into_inferred()
                        .execute(i_s, &slice_type.as_args(*i_s));
                    return Inferred::new_any(AnyCause::Todo);
                }
                match &self.args {
                    TupleArgs::ArbitraryLen(t) => Inferred::from_type(t.as_ref().clone()),
                    _ => {
                        let out_of_range = |variadic_max_len| {
                            slice_type.as_argument_node_ref().add_issue(
                                i_s,
                                IssueType::TupleIndexOutOfRange { variadic_max_len },
                            );
                            Some(Inferred::new_any_from_error())
                        };
                        index_inf
                            .run_on_int_literals(i_s, |index| match &self.args {
                                TupleArgs::FixedLen(ts) => {
                                    let index = if index < 0 {
                                        let index = ts.len() as isize + index;
                                        match index.try_into() {
                                            Ok(index) => index,
                                            Err(_) => return out_of_range(None),
                                        }
                                    } else {
                                        index as usize
                                    };
                                    if let Some(t) = ts.as_ref().get(index) {
                                        Some(Inferred::from_type(t.clone()))
                                    } else {
                                        out_of_range(None)
                                    }
                                }
                                TupleArgs::WithUnpack(with_unpack) => {
                                    if index < 0 {
                                        let index = -index as usize - 1;
                                        let after_len = with_unpack.after.len();
                                        let max_len = after_len + with_unpack.before.len();
                                        Some(Inferred::from_type(if index >= max_len {
                                            return out_of_range(Some(max_len));
                                        } else if index < after_len {
                                            with_unpack.after[after_len - index - 1].clone()
                                        } else {
                                            match &with_unpack.unpack {
                                                TupleUnpack::TypeVarTuple(tvt) => {
                                                    i_s.db.python_state.object_type()
                                                }
                                                TupleUnpack::ArbitraryLen(t) => {
                                                    simplified_union_from_iterators(
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
                                        let index = index as usize;
                                        let before_len = with_unpack.before.len();
                                        let max_len = before_len + with_unpack.after.len();
                                        Some(Inferred::from_type(if index >= max_len {
                                            return out_of_range(Some(max_len));
                                        } else if index < before_len {
                                            with_unpack.before[index].clone()
                                        } else {
                                            match &with_unpack.unpack {
                                                TupleUnpack::TypeVarTuple(tvt) => {
                                                    i_s.db.python_state.object_type()
                                                }
                                                TupleUnpack::ArbitraryLen(t) => {
                                                    simplified_union_from_iterators(
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
                                Inferred::from_type(self.simplified_union_of_tuple_entries(i_s))
                            })
                    }
                }
            }
            SliceTypeContent::Slices(_) | SliceTypeContent::Starred(_) => {
                todo!()
            }
            SliceTypeContent::Slice(slice) => slice
                .callback_on_tuple_indexes(i_s, |start, end, step| {
                    if step == 0 {
                        slice_type
                            .as_node_ref()
                            .add_issue(i_s, IssueType::TupleSliceStepCannotBeZero);
                        return Inferred::from_type(Type::Tuple(
                            Self::new_arbitrary_length_with_any_from_error(),
                        ));
                    }
                    match &self.args {
                        TupleArgs::FixedLen(ts) => {
                            Inferred::from_type(Type::Tuple(Tuple::new_fixed_length({
                                let (start, end) = if step < 0 {
                                    let swapped_start = match end {
                                        Some(end) if end < 0 => ts.len() as isize + end + 1,
                                        Some(end) => end + 1,
                                        None => 0,
                                    };
                                    let swapped_end = match start {
                                        Some(start) if start < 0 => ts.len() as isize + start + 1,
                                        Some(start) => start + 1,
                                        None => ts.len() as isize,
                                    };
                                    (swapped_start, swapped_end)
                                } else {
                                    let end = match end {
                                        Some(end) if end < 0 => ts.len() as isize + end,
                                        Some(end) => end,
                                        None => ts.len() as isize,
                                    };
                                    let start = start.unwrap_or(0);
                                    let start = if start < 0 {
                                        ts.len() as isize + start
                                    } else {
                                        start
                                    };
                                    (start, end)
                                };
                                // Ensure tuple bounds
                                let start = (start.max(0) as usize).min(ts.len());
                                let end = (end.max(start as isize) as usize).min(ts.len());
                                // Fetch tuples
                                if step < 0 {
                                    ts[start..end]
                                        .iter()
                                        .rev()
                                        .step_by(-step as usize)
                                        .cloned()
                                        .collect()
                                } else {
                                    ts[start..end]
                                        .iter()
                                        .step_by(step as usize)
                                        .cloned()
                                        .collect()
                                }
                            })))
                        }
                        TupleArgs::WithUnpack(with_unpack) => {
                            Inferred::from_type(Type::Tuple(Tuple::new(TupleArgs::WithUnpack({
                                let ambiguous = || {
                                    slice_type
                                        .as_node_ref()
                                        .add_issue(i_s, IssueType::AmbigousSliceOfVariadicTuple);
                                    Inferred::from_type(Type::Tuple(
                                        Self::new_arbitrary_length_with_any_from_error(),
                                    ))
                                };
                                if step == 1 {
                                    let start = start.unwrap_or(0);
                                    let before_len = with_unpack.before.len() as isize;
                                    let after_len = with_unpack.after.len() as isize;
                                    let end = end.unwrap_or(0);
                                    if start > before_len || end > before_len {
                                        return ambiguous();
                                    }
                                    if -end > after_len || -start > after_len {
                                        return ambiguous();
                                    }
                                    if end > 0 {
                                        if start < 0 {
                                            return ambiguous();
                                        }
                                        todo!()
                                    } else if start < 0 {
                                        todo!()
                                    } else {
                                        WithUnpack {
                                            before: with_unpack
                                                .before
                                                .iter()
                                                .skip(start as usize)
                                                .cloned()
                                                .collect(),
                                            unpack: with_unpack.unpack.clone(),
                                            after: with_unpack
                                                .after
                                                .iter()
                                                .rev()
                                                .skip(-end as usize)
                                                .rev()
                                                .cloned()
                                                .collect(),
                                        }
                                    }
                                } else if step == -1 {
                                    if start.is_some() || end.is_some() {
                                        todo!()
                                    }
                                    WithUnpack {
                                        before: with_unpack.after.iter().rev().cloned().collect(),
                                        unpack: with_unpack.unpack.clone(),
                                        after: with_unpack.before.iter().rev().cloned().collect(),
                                    }
                                } else {
                                    return ambiguous();
                                }
                            }))))
                        }
                        TupleArgs::ArbitraryLen(t) => {
                            Inferred::from_type(Type::Tuple(Rc::new(self.clone())))
                        }
                    }
                })
                .unwrap_or_else(|| {
                    Inferred::from_type(Type::Tuple(Tuple::new_arbitrary_length(
                        self.simplified_union_of_tuple_entries(i_s),
                    )))
                }),
        }
    }

    pub fn find_in_type(&self, check: &mut impl FnMut(&Type) -> bool) -> bool {
        match &self.args {
            TupleArgs::FixedLen(ts) => ts.iter().any(|t| t.find_in_type(check)),
            TupleArgs::ArbitraryLen(t) => t.find_in_type(check),
            TupleArgs::WithUnpack(with_unpack) => with_unpack.find_in_type(check),
        }
    }

    fn simplified_union_of_tuple_entries(&self, i_s: &InferenceState) -> Type {
        match &self.args {
            TupleArgs::FixedLen(ts) => simplified_union_from_iterators(i_s, ts.iter()),
            TupleArgs::WithUnpack(with_unpack) => match &with_unpack.unpack {
                TupleUnpack::TypeVarTuple(tvt) => i_s.db.python_state.object_type(),
                TupleUnpack::ArbitraryLen(t) => simplified_union_from_iterators(
                    i_s,
                    with_unpack
                        .before
                        .iter()
                        .chain(std::iter::once(t))
                        .chain(with_unpack.after.iter()),
                ),
            },
            TupleArgs::ArbitraryLen(t) => (**t).clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TupleUnpack {
    TypeVarTuple(TypeVarTupleUsage),
    ArbitraryLen(Type),
}

impl TupleUnpack {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::TypeVarTuple(t) => format_data.format_type_var_like(
                &TypeVarLikeUsage::TypeVarTuple(t.clone()),
                ParamsStyle::Unreachable,
            ),
            Self::ArbitraryLen(t) => format!("Tuple[{}, ...]", t.format(format_data)).into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct WithUnpack {
    pub before: Rc<[Type]>,
    pub unpack: TupleUnpack,
    pub after: Rc<[Type]>,
}

impl WithUnpack {
    pub fn with_empty_before_and_after(unpack: TupleUnpack) -> Self {
        Self {
            before: Rc::from([]),
            unpack,
            after: Rc::from([]),
        }
    }

    fn format(&self, format_data: &FormatData) -> Box<str> {
        join_with_commas(
            self.before
                .iter()
                .map(|t| t.format(format_data).into())
                .chain(std::iter::once(format!(
                    "Unpack[{}]",
                    self.unpack.format(format_data)
                )))
                .chain(self.after.iter().map(|t| t.format(format_data).into())),
        )
        .into()
    }

    pub fn find_in_type(&self, check: &mut impl FnMut(&Type) -> bool) -> bool {
        self.before.iter().any(|t| t.find_in_type(check))
            || match &self.unpack {
                TupleUnpack::TypeVarTuple(_) => false,
                TupleUnpack::ArbitraryLen(t) => t.find_in_type(check),
            }
            || self.before.iter().any(|t| t.find_in_type(check))
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveType>>,
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

#[derive(Debug, Clone, PartialEq)]
pub enum TupleArgs {
    WithUnpack(WithUnpack),
    FixedLen(Rc<[Type]>),
    ArbitraryLen(Box<Type>),
}

impl TupleArgs {
    pub fn is_any(&self) -> bool {
        match self {
            Self::ArbitraryLen(t) => matches!(t.as_ref(), Type::Any(_)),
            _ => false,
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
        already_checked: &mut Vec<Rc<RecursiveType>>,
    ) -> bool {
        match self {
            Self::FixedLen(ts) => ts.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::ArbitraryLen(t) => t.has_any_internal(i_s, already_checked),
            Self::WithUnpack(with_unpack) => with_unpack.has_any_internal(i_s, already_checked),
        }
    }

    fn common_base_for_all_items(&self, i_s: &InferenceState) -> Type {
        match self {
            Self::FixedLen(ts) => common_base_type(i_s, ts.iter()),
            Self::ArbitraryLen(t) => t.as_ref().clone(),
            Self::WithUnpack(_) => i_s.db.python_state.object_type(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::FixedLen(ts) if ts.is_empty() => Box::from("()"),
            Self::FixedLen(ts) => {
                join_with_commas(ts.iter().map(|g| g.format(format_data).into())).into()
            }
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
                Self::ArbitraryLen(Box::new(t1.merge_matching_parts(db, &t2)))
            }
            (WithUnpack(_), _) => todo!(),
            (_, WithUnpack(_)) => todo!(),
            _ => Tuple::new_arbitrary_length_with_any().args.clone(),
        }
    }

    pub fn add_before_and_after(self, before: Vec<Type>, after: Vec<Type>) -> Self {
        match self {
            TupleArgs::FixedLen(fixed) => TupleArgs::FixedLen({
                before
                    .into_iter()
                    .chain(fixed.iter().cloned())
                    .chain(after)
                    .collect()
            }),
            TupleArgs::WithUnpack(new) => TupleArgs::WithUnpack(WithUnpack {
                before: merge_types(before, new.before),
                unpack: new.unpack,
                after: merge_types(after, new.after),
            }),
            TupleArgs::ArbitraryLen(t) => {
                if before.is_empty() && after.is_empty() {
                    TupleArgs::ArbitraryLen(t)
                } else {
                    TupleArgs::WithUnpack(WithUnpack {
                        before: before.into(),
                        unpack: TupleUnpack::ArbitraryLen(*t),
                        after: after.into(),
                    })
                }
            }
        }
    }
}

fn merge_types(mut original: Vec<Type>, new: Rc<[Type]>) -> Rc<[Type]> {
    if original.is_empty() {
        new
    } else if new.is_empty() {
        original.into()
    } else {
        original.append(&mut rc_slice_into_vec(new));
        original.into()
    }
}

pub(crate) fn lookup_on_tuple<'x>(
    tuple: &'x Rc<Tuple>,
    i_s: &'x InferenceState,
    add_issue: impl Fn(IssueType),
    name: &str,
) -> LookupDetails<'x> {
    lookup_tuple_magic_methods(tuple.clone(), name).or_else(|| {
        let tuple_cls = i_s.db.python_state.tuple_class(i_s.db, &tuple);
        let tuple_instance = Instance::new(tuple_cls, None);
        for (mro_index, class_or_type) in tuple_cls.mro(i_s.db) {
            let (cls, lookup) = class_or_type.lookup_symbol(i_s, name);
            if let Some(inf) = lookup.into_maybe_inferred() {
                let Some(cls) = cls else {
                    unreachable!();
                };
                let Some((lookup, attr_kind)) = inf.bind_instance_descriptors(
                    i_s,
                    tuple_cls.as_type(i_s.db),
                    cls,
                    |issue| add_issue(issue),
                    mro_index,
                ) else {
                    return LookupDetails::none()
                };
                return LookupDetails {
                    class: class_or_type,
                    lookup: LookupResult::UnknownName(lookup),
                    attr_kind,
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

pub fn lookup_tuple_magic_methods(tuple: Rc<Tuple>, name: &str) -> LookupDetails<'static> {
    LookupDetails::new(
        Type::Tuple(tuple.clone()),
        match name {
            "__mul__" | "__rmul__" => {
                LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(
                    CustomBehavior::new_method(tuple_mul, Some(Rc::new(Type::Tuple(tuple)))),
                )))
            }
            "__add__" => LookupResult::UnknownName(Inferred::from_type(Type::CustomBehavior(
                CustomBehavior::new_method(tuple_add, Some(Rc::new(Type::Tuple(tuple)))),
            ))),
            _ => LookupResult::None,
        },
        AttributeKind::DefMethod,
    )
}

fn tuple_add<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Args<'db>,
    result_context: &mut ResultContext,
    on_type_error: OnTypeError<'db, '_>,
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
        || Instance::new(i_s.db.python_state.tuple_class(i_s.db, tuple), None),
    )
}

fn tuple_add_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple1: Rc<Tuple>,
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
    on_type_error: OnTypeError<'db, '_>,
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
        || Instance::new(i_s.db.python_state.tuple_class(i_s.db, tuple), None),
    )
}

fn tuple_mul_internal<'db>(
    i_s: &InferenceState<'db, '_>,
    tuple: Rc<Tuple>,
    args: &dyn Args<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    match &tuple.args {
        TupleArgs::FixedLen(ts) => first.run_on_int_literals(i_s, |int| {
            let int = int.max(0) as usize;
            if int > 10 {
                todo!("Do we really want extremely large tuples?")
            }
            Some(Inferred::from_type(Type::Tuple(Tuple::new_fixed_length(
                ts.iter().cycle().take(int * ts.len()).cloned().collect(),
            ))))
        }),
        TupleArgs::ArbitraryLen(_) => Some(Inferred::from_type(Type::Tuple(tuple))),
        TupleArgs::WithUnpack(_) => todo!(),
    }
}
