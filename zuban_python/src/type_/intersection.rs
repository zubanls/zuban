use std::{cell::Cell, rc::Rc};

use crate::{
    database::FileIndex,
    diagnostics::IssueKind,
    format_data::FormatData,
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{LookupKind, ResultContext},
    type_helpers::LookupDetails,
};

use super::Type;

#[derive(Debug, Clone, PartialEq)]
pub struct Intersection {
    entries: Rc<[Type]>,
}

impl Intersection {
    pub fn new(entries: Rc<[Type]>) -> Self {
        debug_assert!(entries.len() > 1);
        Self { entries }
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        let iterator = self.entries.iter();
        let mut formatted_entries = iterator
            .map(|t| {
                let s = match t {
                    Type::Class(c) => c.class(format_data.db).name().into(),
                    _ => t.format(format_data),
                };
                format!("\"{s}\"")
            })
            .collect::<Vec<_>>();
        let formatted = match formatted_entries.as_slice() {
            [a, b] => {
                format!("{a} and {b}")
            }
            _ => {
                formatted_entries.last_mut().unwrap().insert_str(0, "and ");
                formatted_entries.join(", ")
            }
        };
        format!("<subclass of {formatted }>").into()
    }

    pub fn iter(&self) -> std::slice::Iter<Type> {
        self.entries.iter()
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
                    if had_issue.get() {
                        todo!()
                    }
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
            add_issue(first_issue)
        }
        callable(&Type::Intersection(self.clone()), LookupDetails::none())
    }

    pub(crate) fn from_types(t1: Type, t2: Type) -> Self {
        let mut entries = vec![];
        let mut add = |t| match t {
            Type::Intersection(i) => entries.extend(i.iter().cloned()),
            _ => entries.push(t),
        };
        add(t1);
        add(t2);
        Self::new(Rc::from(entries))
    }
}
