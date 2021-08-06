use super::{Value, ValueKind};

#[derive(Debug)]
pub struct Class {
}

impl Class {
}

impl<'a> Value<'a> for Class {
    fn get_kind(&self) -> ValueKind {
        ValueKind::Class
    }

    fn get_name(&self) -> &'a str {
        todo!()
    }
}
