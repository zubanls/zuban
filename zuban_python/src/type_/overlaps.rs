use crate::{
    inference_state::InferenceState,
    matching::{params::has_overlapping_params, Matcher},
    type_::TupleArgs,
    type_helpers::{Class, TypeOrClass},
};

use super::{Tuple, Type};

impl Type {
    pub fn simple_overlaps(&self, i_s: &InferenceState, other: &Self) -> bool {
        self.overlaps(i_s, &mut Matcher::default(), other)
    }

    pub fn overlaps(&self, i_s: &InferenceState, matcher: &mut Matcher, other: &Self) -> bool {
        // In mypy this is called `is_overlapping_types` and it basically ignores variance and a
        // lot of other concepts to tell use whether two types have any relationship at all.
        // e.g. list[A | B] and list[B | C] overlap.
        match other {
            Type::Union(union_type2) => {
                return union_type2.iter().any(|t| self.overlaps(i_s, matcher, t))
            }
            Type::Any(_) => return true, // This is a fallback
            _ => (),
        }

        match self {
            Type::Class(c1) => {
                if let Type::Class(c2) = other {
                    if let Some(result) =
                        Self::overlaps_class(i_s, matcher, c1.class(i_s.db), c2.class(i_s.db))
                    {
                        return result;
                    }
                }
            }
            Type::Type(t1) => {
                if let Type::Type(t2) = other {
                    return t1.overlaps(i_s, matcher, t2);
                }
            }
            Type::Callable(c1) => {
                if let Type::Callable(c2) = other {
                    return c1.return_type.overlaps(i_s, matcher, &c2.return_type)
                        && has_overlapping_params(i_s, matcher, &c1.params, &c2.params);
                }
            }
            Type::Literal(literal1) => match other {
                Type::Literal(literal2) => return literal1.value(i_s.db) == literal2.value(i_s.db),
                _ => {
                    return i_s
                        .db
                        .python_state
                        .literal_type(&literal1.kind)
                        .overlaps(i_s, matcher, other)
                }
            },
            Type::Tuple(t1) => {
                if let Type::Tuple(t2) = other {
                    return Self::overlaps_tuple(i_s, matcher, t1, t2);
                }
            }
            Type::Union(union) => return union.iter().any(|t| t.overlaps(i_s, matcher, other)),
            _ => (),
        };
        self.is_sub_type_of(i_s, matcher, other).bool()
            || self.is_super_type_of(i_s, matcher, other).bool()
    }

    fn overlaps_tuple(i_s: &InferenceState, matcher: &mut Matcher, t1: &Tuple, t2: &Tuple) -> bool {
        use TupleArgs::*;
        match (&t1.args, &t2.args) {
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
                        overlaps &= type1.overlaps(i_s, matcher, &type2);
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
            (FixedLen(ts1), ArbitraryLen(t2)) => {
                ts1.iter().all(|t1| t1.overlaps(i_s, matcher, &t2))
            }
            (WithUnpack(unpack), ArbitraryLen(t1)) | (ArbitraryLen(t1), WithUnpack(unpack)) => {
                unpack
                    .before
                    .iter()
                    .chain(unpack.after.iter())
                    .all(|t2| t1.overlaps(i_s, matcher, t1))
            }
            (WithUnpack(_), WithUnpack(_)) => todo!(),
            (WithUnpack(_), FixedLen(_)) | (FixedLen(_), WithUnpack(_)) => todo!(),
        }
    }

    pub fn overlaps_class(
        i_s: &InferenceState,
        matcher: &mut Matcher,
        class1: Class,
        class2: Class,
    ) -> Option<bool> {
        let mut check = {
            #[inline]
            |i_s: &InferenceState, c1: Class, c2: Class| {
                (c1.node_ref == c2.node_ref).then(|| {
                    let type_vars = c1.type_vars(i_s);
                    c1.generics()
                        .overlaps(i_s, matcher, c2.generics(), type_vars)
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
}
