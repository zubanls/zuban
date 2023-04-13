use crate::{
    database::{Database, GenericsList, PointLink, RecursiveAlias, SpecialType},
    inference_state::InferenceState,
    matching::FormatData,
    value::Class,
};

#[derive(Debug)]
pub struct InheritedNamedtuple {
    class: PointLink,
    generics: Option<GenericsList>,
}

impl InheritedNamedtuple {
    pub fn new(class: PointLink, generics: Option<GenericsList>) -> Self {
        Self { class, generics }
    }

    fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        Class::from_db_type(db, self.class, &self.generics)
    }
}

impl SpecialType for InheritedNamedtuple {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        Box::from("TODO namedtuple format")
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<std::rc::Rc<RecursiveAlias>>,
    ) -> bool {
        todo!()
    }

    fn has_self_type(&self) -> bool {
        todo!()
    }

    fn name<'a>(&'a self, db: &'a Database) -> &'a str {
        let c = self.class(db);
        c.name2()
    }
}
