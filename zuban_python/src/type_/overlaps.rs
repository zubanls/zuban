use crate::{
    debug,
    inference_state::InferenceState,
    matching::Matcher,
    params::has_overlapping_params,
    type_::{TupleArgs, TupleUnpack},
    type_helpers::{Class, TypeOrClass},
};

use super::{CallableContent, CallableLike, ClassGenerics, Tuple, Type, TypeVarKind, TypedDict};

impl Type {
    pub fn simple_overlaps(&self, i_s: &InferenceState, other: &Self) -> bool {
        self.overlaps(i_s, &mut Matcher::default(), other)
    }

    pub fn overlaps(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Self) -> bool {
        let result = self.overlaps_internal(i_s, matcher, other);
        debug!(
            r#"Overlapping? "{}" and "{}": {result}"#,
            self.format_short(i_s.db),
            other.format_short(i_s.db)
        );
        result
    }

    #[inline]
    fn overlaps_internal(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Self) -> bool {
        // In mypy this is called `is_overlapping_types` and it basically ignores variance and a
        // lot of other concepts to tell use whether two types have any relationship at all.
        // e.g. list[A | B] and list[B | C] overlap.
        if let Type::Union(union) = self {
            return union.iter().any(|t| t.overlaps(i_s, matcher, other));
        }

        match other {
            Type::Union(union_type2) => {
                return union_type2.iter().any(|t| self.overlaps(i_s, matcher, t))
            }
            Type::Any(_) => return true, // This is a fallback
            Type::TypedDict(td) => return td.overlaps(i_s, matcher, other, self),
            Type::Literal(literal2) => {
                return match self {
                    Type::Literal(literal1) => literal1.value(i_s.db) == literal2.value(i_s.db),
                    _ => self.overlaps(i_s, matcher, &literal2.fallback_type(i_s.db)),
                }
            }
            Type::TypeVar(tv) => {
                if let TypeVarKind::Bound(b) = &tv.type_var.kind {
                    return self.overlaps(i_s, matcher, b);
                }
            }
            Type::Type(t2) => return t2.overlaps_type_of_type_against_other(i_s, matcher, self),
            _ => (),
        }

        match self {
            Type::Class(c1) => {
                if let Type::Class(c2) = other {
                    if let Some(result) =
                        overlaps_class(i_s, matcher, c1.class(i_s.db), c2.class(i_s.db))
                    {
                        return result;
                    }
                }
            }
            Type::Type(t1) => return t1.overlaps_type_of_type_against_other(i_s, matcher, other),
            Type::Callable(c1) => {
                if let Type::Callable(c2) = other {
                    return c1.overlaps(i_s, matcher, c2);
                }
            }
            Type::Literal(literal1) => {
                return literal1.fallback_type(i_s.db).overlaps(i_s, matcher, other)
            }
            Type::Tuple(t1) => {
                if let Type::Tuple(t2) = other {
                    return t1.overlaps_tuple(i_s, matcher, t2);
                }
            }
            Type::TypeVar(tv) => {
                if let TypeVarKind::Bound(b) = &tv.type_var.kind {
                    return b.overlaps(i_s, matcher, other);
                }
            }
            Type::TypedDict(td) => return td.overlaps(i_s, matcher, self, other),
            _ => (),
        };
        self.is_sub_type_of(i_s, matcher, other).bool()
            || self.is_super_type_of(i_s, matcher, other).bool()
    }

    fn overlaps_type_of_type_against_other(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        other: &Self,
    ) -> bool {
        match other {
            Type::Type(t2) => self.overlaps(i_s, matcher, t2),
            Type::Class(c) => {
                if let Some(metaclass) = self
                    .maybe_class(i_s.db)
                    .and_then(|c| c.maybe_metaclass(i_s.db))
                {
                    Type::new_class(metaclass, ClassGenerics::None).overlaps(i_s, matcher, other)
                } else {
                    other.is_object(i_s.db)
                        || c.class(i_s.db).is_metaclass(i_s.db)
                            && self.overlaps(i_s, matcher, other)
                }
            }
            Type::Callable(c2) => {
                if let Some(callable_like) = self.type_type_maybe_callable(i_s) {
                    match callable_like {
                        CallableLike::Callable(c1) => c1.overlaps(i_s, matcher, c2),
                        CallableLike::Overload(o) => {
                            o.iter_functions().any(|c1| c1.overlaps(i_s, matcher, c2))
                        }
                    }
                } else {
                    false
                }
            }
            Type::Any(_) => true,
            _ => false,
        }
    }
}

impl Tuple {
    fn overlaps_tuple(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Tuple) -> bool {
        use TupleArgs::*;
        match (&self.args, &other.args) {
            (FixedLen(ts1), FixedLen(ts2)) => {
                let mut value_generics = ts2.iter();
                let mut overlaps = true;
                for type1 in ts1.iter() {
                    /*
                    if matcher.might_have_defined_type_vars() {
                        match type1 {
                            Type::TypeVarLike(t) if t.is_type_var_tuple() => {
                                todo!()
                            }
                            _ => (),
                        }
                    }
                    */
                    if let Some(type2) = value_generics.next() {
                        overlaps &= type1.overlaps(i_s, matcher, type2);
                    } else {
                        overlaps = false;
                    }
                }
                if value_generics.next().is_some() {
                    overlaps = false;
                }
                overlaps
            }
            (ArbitraryLen(t1), ArbitraryLen(t2)) => t1.overlaps(i_s, matcher, t2),
            (ArbitraryLen(t1), FixedLen(ts2)) => ts2.iter().all(|t2| t1.overlaps(i_s, matcher, t2)),
            (FixedLen(ts1), ArbitraryLen(t2)) => ts1.iter().all(|t1| t1.overlaps(i_s, matcher, t2)),
            (WithUnpack(unpack), ArbitraryLen(t1)) | (ArbitraryLen(t1), WithUnpack(unpack)) => {
                unpack
                    .before
                    .iter()
                    .chain(unpack.after.iter())
                    .all(|t2| t1.overlaps(i_s, matcher, t1))
            }
            (WithUnpack(w1), WithUnpack(w2)) => {
                // TODO write tests for WithUnpack when the lengths do not match
                /*
                if w1.before.len() != w2.before.len() || w1.after.len() != w2.after.len() {
                }
                */
                let mut before2_it = w2.before.iter();
                let mut after2_it = w2.after.iter();
                w1.before
                    .iter()
                    .zip(before2_it.by_ref())
                    .all(|(t1, t2)| t1.overlaps(i_s, matcher, t2))
                    && w1
                        .after
                        .iter()
                        .zip(after2_it.by_ref())
                        .all(|(t1, t2)| t1.overlaps(i_s, matcher, t2))
                    && match &w1.unpack {
                        TupleUnpack::ArbitraryLen(t1) => match &w2.unpack {
                            TupleUnpack::TypeVarTuple(_) => todo!(),
                            TupleUnpack::ArbitraryLen(t2) => t1.overlaps(i_s, matcher, t2),
                        },
                        TupleUnpack::TypeVarTuple(tvt1) => {
                            /*
                            let tup_args2 = TupleArgs::WithUnpack(super::WithUnpack {
                                before: before2_it.cloned().collect(),
                                unpack: w2.unpack.clone(),
                                after: after2_it.cloned().collect(),
                            });
                            matcher.match_or_add_type_var_tuple(i_s, tvt1, tup_args2, Variance::Invariant).bool()
                            */
                            todo!()
                        }
                    }
            }
            (WithUnpack(w1), FixedLen(ts2)) => {
                if w1.before.len() + w1.after.len() > ts2.len() {
                    return false;
                }
                let middle2 = &ts2[w1.before.len()..ts2.len() - w1.after.len()];
                w1.before
                    .iter()
                    .zip(ts2.iter())
                    .all(|(t1, t2)| t1.overlaps(i_s, matcher, t2))
                    && w1
                        .after
                        .iter()
                        .rev()
                        .zip(ts2.iter().rev())
                        .all(|(t1, t2)| t1.overlaps(i_s, matcher, t2))
                    && match &w1.unpack {
                        TupleUnpack::ArbitraryLen(t1) => {
                            middle2.iter().all(|t2| t1.overlaps(i_s, matcher, t2))
                        }
                        TupleUnpack::TypeVarTuple(tvt1) => todo!(),
                    }
            }
            (FixedLen(_), WithUnpack(_)) => other.overlaps_tuple(i_s, matcher, self),
        }
    }
}

fn overlaps_class(
    i_s: &InferenceState,
    matcher: &mut Matcher,
    class1: Class,
    class2: Class,
) -> Option<bool> {
    let mut check = {
        #[inline]
        |i_s: &InferenceState, c1: Class, c2: Class| {
            (c1.node_ref == c2.node_ref).then(|| {
                let mut matches = true;
                for (t1, t2) in c1.generics().iter(i_s.db).zip(c2.generics().iter(i_s.db)) {
                    matches &= t1.overlaps(i_s, matcher, t2);
                }
                matches
            })
        }
    };

    for (_, c1) in class1.mro(i_s.db) {
        if let TypeOrClass::Class(c1) = c1 {
            if let result @ Some(_) = check(i_s, c1, class2) {
                return result;
            }
        }
    }
    for (_, c2) in class2.mro(i_s.db) {
        if let TypeOrClass::Class(c2) = c2 {
            if let result @ Some(_) = check(i_s, class1, c2) {
                return result;
            }
        }
    }
    None
}

impl TypedDict {
    pub fn overlaps(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        original: &Type,
        other: &Type,
    ) -> bool {
        match other {
            Type::TypedDict(_) => {
                // TODO this should actually check overlaps of its content and not normal matching
                original.is_sub_type_of(i_s, matcher, other).bool()
                    || original.is_super_type_of(i_s, matcher, other).bool()
            }
            _ => {
                self.overlaps_with_mapping(i_s, matcher, other)
                    || original.is_sub_type_of(i_s, matcher, other).bool()
            }
        }
    }

    fn overlaps_with_mapping(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        other: &Type,
    ) -> bool {
        // Mypy has a function for this called "typed_dict_mapping_overlap". Its docstring
        // describes really well how this works.
        other
            .find_class_in_mro(i_s.db, i_s.db.python_state.mapping_node_ref())
            .is_some_and(|mapping| {
                let key = mapping.nth_type_argument(i_s.db, 0);
                let value = mapping.nth_type_argument(i_s.db, 1);
                if !key.overlaps(i_s, matcher, &i_s.db.python_state.str_type()) {
                    return false;
                }

                // Special case for e.g. Matching of X == {}
                if key.is_never() || value.is_never() {
                    return self.iter_required_members(i_s.db).next().is_none();
                }

                let mut had_required = false;
                // All required members must overlap
                for member in self.members(i_s.db).iter() {
                    if member.required {
                        had_required = true;
                        if !member.type_.overlaps(i_s, matcher, &value) {
                            return false;
                        }
                    }
                }
                if had_required {
                    return true;
                }
                // In case there were no required members, as long as any optional members overlap we
                // are fine.
                self.iter_optional_members(i_s.db)
                    .any(|member| member.type_.overlaps(i_s, matcher, &value))
            })
    }
}

impl CallableContent {
    pub fn overlaps(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Self) -> bool {
        self.return_type.overlaps(i_s, matcher, &other.return_type)
            && has_overlapping_params(i_s, matcher, &self.params, &other.params)
    }
}
