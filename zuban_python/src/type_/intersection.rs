use std::rc::Rc;

use crate::format_data::FormatData;

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
        let formatted = iterator
            .map(|t| t.format(format_data))
            .collect::<Vec<_>>()
            .join(", ");
        format!("<subclass of {formatted }>").into()
    }
}
