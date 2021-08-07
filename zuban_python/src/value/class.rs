use super::{Value, ValueKind};
use crate::file::{File};

#[derive(Debug)]
pub struct Class<'a> {
    file: &'a dyn File,
}

impl<'a> Class<'a> {
    pub fn new(file: &'a dyn File) -> Self {
        Self {file}
    }
}

impl<'a> Value<'a> for Class<'a> {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        todo!()
    }
}
