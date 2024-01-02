use std::{borrow::Cow, cell::OnceCell, rc::Rc};

use super::{
    common_base_type, simplified_union_from_iterators, utils::method_with_fallback, CustomBehavior,
    FormatStyle, GenericItem, GenericsList, RecursiveType, TypeVarLikeUsage, TypeVarTupleUsage,
};
use crate::{
    arguments::Arguments,
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
    utils::join_with_commas,
};

thread_local! {
    static ARBITRARY_TUPLE: Rc<Tuple> = Rc::new(Tuple::new_arbitrary_length(Type::Any(AnyCause::Todo)));
}

#[derive(Debug, Clone, PartialEq)]
pub struct Tuple {
    pub args: TupleTypeArguments,
    pub(super) tuple_class_generics: OnceCell<GenericsList>,
}

impl Tuple {
    pub fn new(args: TupleTypeArguments) -> Self {
        Self {
            args,
            tuple_class_generics: OnceCell::new(),
        }
    }

    pub fn new_fixed_length(args: Rc<[Type]>) -> Self {
        Self::new(TupleTypeArguments::FixedLength(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleTypeArguments::ArbitraryLength(Box::new(arg)))
    }

    pub fn new_arbitrary_length_with_any() -> Rc<Self> {
        ARBITRARY_TUPLE.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        self.tuple_class_generics.get_or_init(|| {
            GenericsList::new_generics(Rc::new([GenericItem::TypeArgument(
                self.args.common_base_type(&InferenceState::new(db)),
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
            TupleTypeArguments::FixedLength(ts) => IteratorContent::new_tuple(ts.clone()),
            TupleTypeArguments::ArbitraryLength(t) => {
                IteratorContent::Inferred(Inferred::from_type(t.as_ref().clone()))
            }
            TupleTypeArguments::WithUnpack(_) => todo!(),
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
                    TupleTypeArguments::ArbitraryLength(t) => {
                        Inferred::from_type(t.as_ref().clone())
                    }
                    TupleTypeArguments::FixedLength(ts) => {
                        let out_of_range = || {
                            slice_type
                                .as_argument_node_ref()
                                .add_issue(i_s, IssueType::TupleIndexOutOfRange);
                            Some(Inferred::new_any_from_error())
                        };
                        index_inf
                            .run_on_int_literals(i_s, |index| {
                                let index = if index < 0 {
                                    let index = ts.len() as isize + index;
                                    match index.try_into() {
                                        Ok(index) => index,
                                        Err(_) => return out_of_range(),
                                    }
                                } else {
                                    index as usize
                                };
                                if let Some(t) = ts.as_ref().get(index) {
                                    Some(Inferred::from_type(t.clone()))
                                } else {
                                    return out_of_range();
                                }
                            })
                            .unwrap_or_else(|| {
                                Inferred::from_type(simplified_union_of_tuple_entries(i_s, ts))
                            })
                    }
                    TupleTypeArguments::WithUnpack(_) => todo!(),
                }
            }
            SliceTypeContent::Slices(slices) => {
                todo!()
            }
            SliceTypeContent::Slice(slice) => match &self.args {
                TupleTypeArguments::ArbitraryLength(t) => {
                    todo!()
                }
                args @ TupleTypeArguments::FixedLength(ts) => slice
                    .callback_on_tuple_indexes(i_s, ts, |start, end, step| {
                        Inferred::from_type(Type::Tuple(Rc::new(Tuple::new_fixed_length(
                            match step {
                                1 => ts[start..end].into(),
                                n if n > 1 => {
                                    ts[start..end].iter().step_by(n as usize).cloned().collect()
                                }
                                n if n < 0 => {
                                    todo!()
                                }
                                _ => unreachable!(),
                            },
                        ))))
                    })
                    .unwrap_or_else(|| {
                        Inferred::from_type(Type::Tuple(Rc::new(Tuple::new_arbitrary_length(
                            simplified_union_of_tuple_entries(i_s, ts),
                        ))))
                    }),
                TupleTypeArguments::WithUnpack(_) => todo!(),
            },
        }
    }

    pub fn find_in_type(&self, check: &impl Fn(&Type) -> bool) -> bool {
        match &self.args {
            TupleTypeArguments::FixedLength(ts) => ts.iter().any(|t| t.find_in_type(check)),
            TupleTypeArguments::ArbitraryLength(t) => t.find_in_type(check),
            TupleTypeArguments::WithUnpack(with_unpack) => with_unpack.find_in_type(check),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TupleUnpack {
    TypeVarTuple(TypeVarTupleUsage),
    Tuple(Rc<Tuple>),
}

impl TupleUnpack {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::TypeVarTuple(t) => format_data.format_type_var_like(
                &TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(t)),
                ParamsStyle::Unreachable,
            ),
            Self::Tuple(tup) => tup.format(format_data),
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

    pub fn find_in_type(&self, check: &impl Fn(&Type) -> bool) -> bool {
        self.before.iter().any(|t| t.find_in_type(check))
            || match &self.unpack {
                TupleUnpack::TypeVarTuple(_) => false,
                TupleUnpack::Tuple(tup) => tup.find_in_type(check),
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
                TupleUnpack::Tuple(tup) => tup.args.has_any_internal(i_s, already_checked),
            }
            || self
                .after
                .iter()
                .any(|t| t.has_any_internal(i_s, already_checked))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TupleTypeArguments {
    WithUnpack(WithUnpack),
    FixedLength(Rc<[Type]>),
    ArbitraryLength(Box<Type>),
}

impl TupleTypeArguments {
    pub fn is_any(&self) -> bool {
        match self {
            Self::ArbitraryLength(t) => matches!(t.as_ref(), Type::Any(_)),
            _ => false,
        }
    }

    pub fn has_any(&self, i_s: &InferenceState) -> bool {
        self.has_any_internal(i_s, &mut Vec::new())
    }

    pub(super) fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<Rc<RecursiveType>>,
    ) -> bool {
        match self {
            Self::FixedLength(ts) => ts.iter().any(|t| t.has_any_internal(i_s, already_checked)),
            Self::ArbitraryLength(t) => t.has_any_internal(i_s, already_checked),
            Self::WithUnpack(with_unpack) => with_unpack.has_any_internal(i_s, already_checked),
        }
    }

    fn common_base_type(&self, i_s: &InferenceState) -> Type {
        match self {
            Self::FixedLength(ts) => common_base_type(i_s, ts.iter()),
            Self::ArbitraryLength(t) => t.as_ref().clone(),
            Self::WithUnpack(_) => i_s.db.python_state.object_type(),
        }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        match self {
            Self::FixedLength(ts) if ts.is_empty() => Box::from("()"),
            Self::FixedLength(ts) => {
                join_with_commas(ts.iter().map(|g| g.format(format_data).into())).into()
            }
            Self::ArbitraryLength(t) => format!("{}, ...", t.format(format_data)).into(),
            Self::WithUnpack(unpack) => unpack.format(format_data),
        }
    }

    pub fn search_type_vars<C: FnMut(TypeVarLikeUsage)>(&self, found_type_var: &mut C) {
        match self {
            TupleTypeArguments::FixedLength(ts) => {
                for t in ts.iter() {
                    t.search_type_vars(found_type_var)
                }
            }
            TupleTypeArguments::ArbitraryLength(t) => t.search_type_vars(found_type_var),
            TupleTypeArguments::WithUnpack(with_unpack) => {
                for t in with_unpack.before.iter() {
                    t.search_type_vars(found_type_var)
                }
                match &with_unpack.unpack {
                    TupleUnpack::TypeVarTuple(tvt) => {
                        found_type_var(TypeVarLikeUsage::TypeVarTuple(Cow::Borrowed(tvt)))
                    }
                    TupleUnpack::Tuple(tup) => tup.args.search_type_vars(found_type_var),
                }
                for t in with_unpack.after.iter() {
                    t.search_type_vars(found_type_var)
                }
            }
        }
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

fn simplified_union_of_tuple_entries(i_s: &InferenceState, entries: &[Type]) -> Type {
    let highest_union_format_index = entries
        .iter()
        .map(|t| t.highest_union_format_index())
        .max()
        .unwrap_or(0);
    simplified_union_from_iterators(
        i_s,
        entries.iter().cloned().enumerate(),
        highest_union_format_index,
        false,
    )
}

fn tuple_add<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
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
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    if let TupleTypeArguments::FixedLength(ts1) = &tuple1.args {
        for (_, type_or_class) in first.as_cow_type(i_s).mro(i_s.db) {
            if let TypeOrClass::Type(t) = type_or_class {
                if let Type::Tuple(tuple2) = t.as_ref() {
                    if let TupleTypeArguments::FixedLength(ts2) = &tuple2.args {
                        return Some(Inferred::from_type(Type::Tuple(Rc::new(
                            Tuple::new_fixed_length(
                                ts1.iter().chain(ts2.iter()).cloned().collect(),
                            ),
                        ))));
                    }
                }
            }
        }
    }
    None
}
fn tuple_mul<'db>(
    i_s: &InferenceState<'db, '_>,
    args: &dyn Arguments<'db>,
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
    args: &dyn Arguments<'db>,
) -> Option<Inferred> {
    let first = args.maybe_single_positional_arg(i_s, &mut ResultContext::Unknown)?;
    match &tuple.args {
        TupleTypeArguments::FixedLength(ts) => first.run_on_int_literals(i_s, |int| {
            let int = int.max(0) as usize;
            if int > 10 {
                todo!("Do we really want extremely large tuples?")
            }
            Some(Inferred::from_type(Type::Tuple(Rc::new(
                Tuple::new_fixed_length(ts.iter().cycle().take(int * ts.len()).cloned().collect()),
            ))))
        }),
        TupleTypeArguments::ArbitraryLength(_) => Some(Inferred::from_type(Type::Tuple(tuple))),
        TupleTypeArguments::WithUnpack(_) => todo!(),
    }
}
