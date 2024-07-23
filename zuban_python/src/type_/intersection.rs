use std::{borrow::Cow, cell::Cell, rc::Rc};

use crate::{
    database::FileIndex,
    diagnostics::IssueKind,
    file::check_multiple_inheritance,
    format_data::FormatData,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupKind, ResultContext},
    type_helpers::{linearize_mro_and_return_linearizable, LookupDetails, TypeOrClass},
};

use super::{AnyCause, Type, UnionEntry};

#[derive(Debug, Clone, PartialEq)]
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
            Type::Intersection(i) => entries.extend(i.iter().cloned()),
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
            (Type::Union(u), _) => {
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

        //Subclass of "C", "B", and "A" cannot exist: would have incompatible method signatures
        let mut intersection = Self::from_types(t1.clone(), t2.clone());

        let mut had_issue = false;
        let fmt_intersection = |intersection: &Self| {
            intersection
                .format_names(&FormatData::new_short(i_s.db), true)
                .into()
        };
        for t in intersection.iter() {
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
                    intersection.iter().map(|t| match t.maybe_class(i_s.db) {
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
        format!("<subclass of {}>", self.format_names(format_data, false)).into()
    }

    pub(crate) fn format_names(&self, format_data: &FormatData, with_generics: bool) -> String {
        let iterator = self.entries.iter();
        let mut formatted_entries = iterator
            .map(|t| {
                let s = match t {
                    Type::Class(c) if !with_generics => c.class(format_data.db).name().into(),
                    Type::Tuple(_) if !with_generics => "tuple".into(),
                    Type::NewType(n) if !with_generics => n.name(format_data.db).into(),
                    _ => t.format(format_data),
                };
                format!("\"{s}\"")
            })
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

    pub fn iter(&self) -> std::slice::Iter<Type> {
        self.entries.iter()
    }

    pub fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        for t in self.iter() {
            let had_issue = Cell::new(false);
            let result = t.get_item(i_s, None, slice_type, result_context);
            if !had_issue.get() {
                return result;
            }
        }
        Inferred::new_any_from_error()
    }

    pub(crate) fn run_after_lookup_on_each_union_member(
        &self,
        i_s: &InferenceState,
        from_inferred: Option<&Inferred>,
        from_file: FileIndex,
        name: &str,
        kind: LookupKind,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind),
        callable: &mut dyn FnMut(&Type, LookupDetails),
    ) {
        let first_issue = Cell::new(None);
        for t in self.iter() {
            let had_issue = Cell::new(false);
            t.run_after_lookup_on_each_union_member(
                i_s,
                None,
                from_file,
                name,
                kind,
                result_context,
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
