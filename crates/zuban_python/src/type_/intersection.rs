use std::{borrow::Cow, cell::Cell, rc::Rc};

use crate::{
    arguments::Args,
    diagnostics::IssueKind,
    file::check_multiple_inheritance,
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{IteratorContent, OnTypeError, ResultContext},
    type_helpers::{linearize_mro_and_return_linearizable, LookupDetails, TypeOrClass},
};

use super::{AnyCause, CallableParams, FormatStyle, IterInfos, Type, UnionEntry};

type RunOnUnionEntry<'a> =
    &'a mut dyn FnMut(&Type, &dyn Fn(IssueKind), &mut dyn FnMut(&Type, LookupDetails));

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Intersection {
    entries: Rc<[Type]>,
}

impl Intersection {
    pub fn new(entries: Rc<[Type]>) -> Self {
        debug_assert!(entries.len() > 1);
        Self { entries }
    }

    fn from_types(t1: Type, t2: Type) -> Self {
        let mut entries = vec![];
        let mut add = |t| match t {
            Type::Intersection(i) => entries.extend(i.iter_entries().cloned()),
            _ => entries.push(t),
        };
        add(t1);
        add(t2);
        Self::new(Rc::from(entries))
    }

    pub(crate) fn new_instance_intersection(
        i_s: &InferenceState,
        t1: &Type,
        t2: &Type,
        add_issue: &mut dyn FnMut(IssueKind),
    ) -> Result<Type, ()> {
        match (t1, t2) {
            (Type::Type(t1), Type::Type(t2)) => {
                return Self::new_instance_intersection(i_s, t1.as_ref(), t2.as_ref(), add_issue)
                    .map(|out| Type::Type(Rc::new(out)))
            }
            (Type::Union(_), _) => {
                unreachable!("For now this branch should not be reachable")
            }
            (_, Type::Union(u)) => {
                let mut found_issues = vec![];
                let mut new_entries = vec![];
                for entry in u.entries.iter() {
                    if let Ok(type_) = Intersection::new_instance_intersection(
                        i_s,
                        t1,
                        &entry.type_,
                        &mut |issue| found_issues.push(issue),
                    ) {
                        new_entries.push(UnionEntry {
                            type_,
                            format_index: entry.format_index,
                        });
                    }
                }
                return if new_entries.is_empty() {
                    for issue in found_issues {
                        add_issue(issue)
                    }
                    Err(())
                } else {
                    Ok(Type::from_union_entries(new_entries))
                };
            }
            (Type::Self_, _) => {
                return Intersection::new_instance_intersection(
                    i_s,
                    &i_s.current_class().unwrap().as_type(i_s.db),
                    t2,
                    add_issue,
                )
            }
            (_, Type::Self_) => {
                return Intersection::new_instance_intersection(
                    i_s,
                    t1,
                    &i_s.current_class().unwrap().as_type(i_s.db),
                    add_issue,
                )
            }
            _ => (),
        }
        let mut error_if_not_intersectable = |t: &Type| {
            if t == &Type::None {
                add_issue(IssueKind::IntersectionCannotExistDueToFinalClass {
                    intersection: format!(r#""{}" and "NoneType""#, t1.format_short(i_s.db)).into(),
                    final_class: "NoneType".into(),
                })
            }
            Err(())
        };
        if !t1.is_intersectable(i_s.db) {
            return error_if_not_intersectable(t1);
        }
        if !t2.is_intersectable(i_s.db) {
            return error_if_not_intersectable(t2);
        }

        //Subclass of "C", "B", and "A" cannot exist: would have incompatible method signatures
        let mut intersection = Self::from_types(t1.clone(), t2.clone());

        let mut had_issue = false;
        let fmt_intersection = |intersection: &Self| {
            intersection
                .format_names(&FormatData::new_short(i_s.db))
                .into()
        };
        for t in intersection.iter_entries() {
            if let Some(cls) = t.maybe_class(i_s.db) {
                if cls.use_cached_class_infos(i_s.db).is_final {
                    add_issue(IssueKind::IntersectionCannotExistDueToFinalClass {
                        intersection: fmt_intersection(&intersection),
                        final_class: cls.name().into(),
                    });
                    had_issue = true;
                }
            }
        }
        if had_issue {
            return Err(());
        }

        let linearizable = linearize_mro_and_return_linearizable(i_s, &intersection.entries).1;
        if !linearizable {
            add_issue(IssueKind::IntersectionCannotExistDueToInconsistentMro {
                intersection: fmt_intersection(&intersection),
            });
            return Err(());
        }

        let check_multi_inheritance = |intersection: &Self, had_issue: &mut _| {
            check_multiple_inheritance(
                i_s,
                || {
                    intersection
                        .iter_entries()
                        .map(|t| match t.maybe_class(i_s.db) {
                            Some(c) => TypeOrClass::Class(c),
                            None => TypeOrClass::Type(Cow::Borrowed(t)),
                        })
                },
                |_| true,
                |_| *had_issue = true,
            );
        };

        check_multi_inheritance(&intersection, &mut had_issue);
        if had_issue {
            // Try the other direction, because that might be valid.
            // Other checks are not important anymore, because they don't depend on direction.
            // (The linearization check of course does, but only if a class is a subtype of another
            // one, which shouldn't be the case here anymore).
            had_issue = false;
            let old_intersection = intersection;
            intersection = Self::from_types(t2.clone(), t1.clone());
            check_multi_inheritance(&intersection, &mut had_issue);
            if had_issue {
                // Reset to the original intersection to always have the same order of error messages
                intersection = old_intersection;
            }
        }

        if had_issue {
            add_issue(
                IssueKind::IntersectionCannotExistDueToIncompatibleMethodSignatures {
                    intersection: fmt_intersection(&intersection),
                },
            );
            return Err(());
        }
        Ok(Type::Intersection(intersection))
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let mut format_data = *format_data;
        // For whatever reason, the names are always formatted as qualified names
        format_data.style = FormatStyle::MypyRevealType;
        if self.entries.len() == 2
            && matches!(&self.entries[0], Type::Callable(c) if matches!(c.params, CallableParams::Any(_)))
        {
            // Mypy special formatting
            format!(
                "<callable subtype of {}>",
                self.entries[1].format_short(format_data.db)
            )
            .into()
        } else {
            format!("<subclass of {}>", self.format_names(&format_data)).into()
        }
    }

    fn format_names(&self, format_data: &FormatData) -> String {
        let iterator = self.entries.iter();
        let mut formatted_entries = iterator
            .map(|t| format!("\"{}\"", t.format(format_data)))
            .collect::<Vec<_>>();
        match formatted_entries.as_slice() {
            [a, b] => {
                format!("{a} and {b}")
            }
            _ => {
                formatted_entries.last_mut().unwrap().insert_str(0, "and ");
                formatted_entries.join(", ")
            }
        }
    }

    pub fn iter_entries(&self) -> std::slice::Iter<Type> {
        self.entries.iter()
    }

    fn wrap_first_non_failing<T>(
        &self,
        mut callable: impl FnMut(&Type, &dyn Fn(IssueKind)) -> T,
    ) -> Result<T, IssueKind> {
        let first_issue = Cell::new(None);
        for t in self.iter_entries() {
            let had_issue = Cell::new(false);
            let result = callable(t, &|issue| {
                first_issue.set(first_issue.take().or(Some(issue)));
                had_issue.set(true);
            });
            if !had_issue.get() {
                return Ok(result);
            }
        }
        Err(first_issue.into_inner().unwrap())
    }

    pub(crate) fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind),
    ) -> Inferred {
        self.wrap_first_non_failing(|t, add_issue| {
            t.get_item_internal(i_s, None, slice_type, result_context, add_issue)
        })
        .unwrap_or_else(|first_issue| {
            add_issue(first_issue);
            Inferred::new_any_from_error()
        })
    }

    pub(crate) fn execute<'db>(
        &self,
        i_s: &InferenceState<'db, '_>,
        args: &dyn Args<'db>,
        result_context: &mut ResultContext,
        on_type_error: OnTypeError,
    ) -> Inferred {
        self.wrap_first_non_failing(|t, _| {
            t.execute(i_s, None, args, result_context, on_type_error)
        })
        .unwrap_or_else(|first_issue| {
            args.add_issue(i_s, first_issue);
            Inferred::new_any_from_error()
        })
    }

    pub(crate) fn iter(&self, i_s: &InferenceState, infos: IterInfos) -> IteratorContent {
        self.wrap_first_non_failing(|t, add_issue| {
            t.iter(i_s, infos.with_different_add_issue(add_issue))
        })
        .unwrap_or_else(|first_issue| {
            infos.add_issue(first_issue);
            IteratorContent::Inferred(Inferred::new_any_from_error())
        })
    }

    pub(crate) fn run_after_lookup_on_each_union_member(
        &self,
        run_on_entry: RunOnUnionEntry,
        add_issue: &dyn Fn(IssueKind),
        callable: &mut dyn FnMut(&Type, LookupDetails),
    ) {
        let first_issue = Cell::new(None);
        for t in self.iter_entries() {
            let had_issue = Cell::new(false);
            run_on_entry(
                t,
                &|issue| {
                    had_issue.set(true);
                    first_issue.set(first_issue.take().or(Some(issue)));
                },
                &mut |on_t, l| {
                    if l.lookup.is_some() {
                        callable(on_t, l)
                    } else {
                        had_issue.set(true);
                    }
                },
            );
            if !had_issue.get() {
                return;
            }
        }
        if let Some(first_issue) = first_issue.into_inner() {
            add_issue(first_issue);
            callable(
                &Type::Intersection(self.clone()),
                LookupDetails::any(AnyCause::FromError),
            )
        } else {
            callable(&Type::Intersection(self.clone()), LookupDetails::none())
        }
    }
}
