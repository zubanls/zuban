use std::{cell::OnceCell, rc::Rc};

use crate::{
    database::Database, inference_state::InferenceState, matching::FormatData, type_::Type,
};

use super::{FormatStyle, GenericItem, GenericsList, TupleTypeArguments, TypeOrTypeVarTuple};

thread_local! {
    static ARBITRARY_TUPLE: Rc<TupleContent> = Rc::new(TupleContent::new_arbitrary_length(Type::Any));
}

#[derive(Debug, Clone, PartialEq)]
pub struct TupleContent {
    pub args: TupleTypeArguments,
    pub(super) tuple_class_generics: OnceCell<GenericsList>,
}

impl TupleContent {
    pub fn new(args: TupleTypeArguments) -> Self {
        Self {
            args,
            tuple_class_generics: OnceCell::new(),
        }
    }

    pub fn new_fixed_length(args: Rc<[TypeOrTypeVarTuple]>) -> Self {
        Self::new(TupleTypeArguments::FixedLength(args))
    }

    pub fn new_arbitrary_length(arg: Type) -> Self {
        Self::new(TupleTypeArguments::ArbitraryLength(Box::new(arg)))
    }

    pub fn new_empty() -> Rc<Self> {
        ARBITRARY_TUPLE.with(|t| t.clone())
    }

    pub fn tuple_class_generics(&self, db: &Database) -> &GenericsList {
        self.tuple_class_generics.get_or_init(|| {
            GenericsList::new_generics(Rc::new([GenericItem::TypeArgument(
                self.args.common_base_type(&InferenceState::new(db)),
            )]))
        })
    }

    pub fn format(&self, format_data: &FormatData) -> Box<str> {
        self.format_with_fallback(format_data, "")
    }

    pub fn format_with_fallback(&self, format_data: &FormatData, fallback: &str) -> Box<str> {
        let base = match format_data.style {
            FormatStyle::Short => "tuple",
            FormatStyle::Qualified | FormatStyle::MypyRevealType => "builtins.tuple",
        };
        format!("{base}[{}{fallback}]", self.args.format(format_data)).into()
    }
}
