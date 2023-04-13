use crate::{
    database::{Database, GenericsList, PointLink, RecursiveAlias, SpecialType, Variance},
    debug,
    inference_state::InferenceState,
    matching::{FormatData, Match, Matcher, Type},
    node_ref::NodeRef,
    value::{Class, LookupResult, Value},
    ValueKind,
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

    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name<'a>(&'a self, db: &'a Database) -> &'a str {
        let c = self.class(db);
        c.name2()
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        debug!("TODO namedtuple");
        self.class(i_s.db).lookup_internal(i_s, node_ref, name)
    }

    fn matches_internal(
        &self,
        i_s: &InferenceState,
        matcher: &mut Matcher,
        value_type: &Type,
        variance: Variance,
    ) -> Match {
        debug!("TODO namedtuple");
        Match::new_true()
    }
}
