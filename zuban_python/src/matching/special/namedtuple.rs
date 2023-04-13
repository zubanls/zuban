use crate::{
    database::{GenericsList, PointLink, RecursiveAlias, SpecialType},
    inference_state::InferenceState,
    matching::FormatData,
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
}
