use std::{
    hash::{Hash, Hasher},
    sync::{Arc, OnceLock},
};

use vfs::FileIndex;

use super::{
    AnyCause, CallableContent, CallableParam, CallableParams, DbString, FormatStyle, FunctionKind,
    Literal, LiteralKind, LookupResult, ParamType, ReplaceTypeVarLikes, StringSlice, Tuple, Type,
    TypeVarLikes, tuple::lookup_tuple_magic_methods,
};
use crate::{
    database::{Database, PointLink},
    diagnostics::IssueKind,
    format_data::{AvoidRecursionFor, FormatData},
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{AttributeKind, Inferred},
    matching::{Generics, IteratorContent, LookupKind},
    new_class,
    result_context::ResultContext,
    type_helpers::LookupDetails,
    utils::join_with_commas,
};

#[derive(Debug, Eq, Clone)]
pub(crate) struct NamedTuple {
    pub name: StringSlice,
    pub __new__: Arc<CallableContent>,
    tuple: OnceLock<Arc<Tuple>>,
}

impl NamedTuple {
    pub fn new(name: StringSlice, __new__: CallableContent) -> Self {
        Self {
            name,
            __new__: Arc::new(__new__),
            tuple: OnceLock::new(),
        }
    }

    pub fn from_params(
        defined_at: PointLink,
        name: StringSlice,
        type_var_likes: TypeVarLikes,
        params: Vec<CallableParam>,
    ) -> Arc<Self> {
        let callable = CallableContent::new_simple(
            Some(DbString::StringSlice(name)),
            None,
            defined_at,
            type_var_likes,
            CallableParams::new_simple(Arc::from(params)),
            Type::Self_,
        );
        Arc::new(NamedTuple::new(name, callable))
    }

    pub fn clone_with_new_init_class(&self, name: StringSlice) -> Arc<NamedTuple> {
        let mut nt = self.clone();
        let mut callable = nt.__new__.as_ref().clone();
        callable.name = Some(DbString::StringSlice(name));
        nt.__new__ = Arc::new(callable);
        Arc::new(nt)
    }

    pub fn params(&self) -> &[CallableParam] {
        // Namedtuple callables contain a first param `Type[Self]` that we should skip.
        &self.__new__.expect_simple_params()[1..]
    }

    pub fn search_param(&self, db: &Database, search_name: &str) -> Option<&CallableParam> {
        self.params()
            .iter()
            .find(|p| p.name.as_ref().unwrap().as_str(db) == search_name)
    }

    pub fn name<'a>(&self, db: &'a Database) -> &'a str {
        self.name.as_str(db)
    }

    pub fn qualified_name(&self, db: &Database) -> String {
        let module = db
            .loaded_python_file(self.name.file_index)
            .qualified_name(db);
        format!("{module}.{}", self.name(db))
    }

    pub fn as_tuple(&self) -> Arc<Tuple> {
        self.tuple
            .get_or_init(|| {
                Tuple::new_fixed_length(
                    self.params()
                        .iter()
                        .map(|t| t.type_.expect_positional_type().clone())
                        .collect(),
                )
            })
            .clone()
    }

    pub fn as_tuple_ref(&self) -> &Tuple {
        self.as_tuple();
        self.tuple.get().unwrap()
    }

    pub fn format_with_name(
        &self,
        format_data: &FormatData,
        name: &str,
        generics: Generics,
    ) -> Box<str> {
        if format_data.style != FormatStyle::MypyRevealType {
            return Box::from(name);
        }
        let params = self.params();
        // We need to check recursions here, because for class definitions of named tuples can
        // recurse with their attributes.
        let avoid = AvoidRecursionFor::NamedTuple(self.__new__.defined_at);
        match format_data.with_seen_recursive_type(avoid) {
            Ok(format_data) => {
                let types = match params.is_empty() {
                    true => "()".into(),
                    false => join_with_commas(params.iter().map(|p| {
                        let t = p.type_.expect_positional_type();
                        match generics {
                            Generics::NotDefinedYet { .. } | Generics::None => {
                                t.format(&format_data)
                            }
                            _ => {
                                let replaced = t.replace_type_var_likes_and_self(
                                    format_data.db,
                                    &mut |usage| {
                                        Some(
                                            generics
                                                .nth_usage(format_data.db, &usage)
                                                .into_generic_item(),
                                        )
                                    },
                                    &|| None,
                                );
                                match replaced {
                                    Some(t) => t.format(&format_data),
                                    None => t.format(&format_data),
                                }
                            }
                        }
                    })),
                };
                format!("tuple[{types}, fallback={name}]",).into()
            }
            Err(_) => Box::from("..."),
        }
    }

    pub fn iter(&self) -> IteratorContent {
        self.as_tuple().iter()
    }

    pub(crate) fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
        add_issue: &dyn Fn(IssueKind) -> bool,
    ) -> Inferred {
        self.as_tuple()
            .get_item(i_s, slice_type, result_context, add_issue)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        name: &str,
        from_type: bool,
        as_self: Option<&dyn Fn() -> Type>,
    ) -> LookupDetails<'static> {
        let mut attr_kind = AttributeKind::Attribute;
        let mut replace_method = |method_name| {
            Type::Callable({
                attr_kind = AttributeKind::DefMethod { is_final: false };
                let mut params = vec![];
                if from_type {
                    params.push(CallableParam::new_anonymous(ParamType::PositionalOnly(
                        as_self.map(|as_self| as_self()).unwrap_or(Type::Self_),
                    )));
                }
                for param in self.params() {
                    let mut new_param = param.clone();
                    new_param.has_default = true;
                    new_param.type_ = ParamType::KeywordOnly(
                        new_param.type_.into_expected_positional_type().clone(),
                    );
                    params.push(new_param);
                }
                Arc::new(CallableContent::new_simple(
                    Some(DbString::Static(method_name)),
                    Some(self.name),
                    PointLink::new(FileIndex(0), 0),
                    i_s.db.python_state.empty_type_var_likes.clone(),
                    CallableParams::new_simple(params.into()),
                    as_self.map(|as_self| as_self()).unwrap_or(Type::Self_),
                ))
            })
        };
        let type_ = match name {
            "__new__" => Type::Callable(self.__new__.clone()),
            "_replace" => replace_method("_replace"),
            "__replace__"
                if i_s
                    .db
                    .project
                    .settings
                    .python_version_or_default()
                    .at_least_3_dot(13) =>
            {
                replace_method("__replace__")
            }
            "_asdict" => Type::Callable({
                attr_kind = AttributeKind::DefMethod { is_final: false };
                let mut params = vec![];
                if from_type {
                    params.push(CallableParam::new_anonymous(ParamType::PositionalOnly(
                        as_self.map(|as_self| as_self()).unwrap_or(Type::Self_),
                    )));
                }
                Arc::new(CallableContent::new_simple(
                    Some(DbString::Static("_as_dict")),
                    Some(self.name),
                    PointLink::new(FileIndex(0), 0),
                    i_s.db.python_state.empty_type_var_likes.clone(),
                    CallableParams::new_simple(params.into()),
                    new_class!(
                        i_s.db.python_state.dict_node_ref().as_link(),
                        i_s.db.python_state.str_type(),
                        Type::Any(AnyCause::Explicit),
                    ),
                ))
            }),
            "_make" => Type::Callable({
                attr_kind = AttributeKind::Classmethod { is_final: false };
                let mut params = vec![];
                if as_self.is_none() {
                    params.push(CallableParam::new_anonymous(ParamType::PositionalOnly(
                        i_s.db.python_state.type_of_self.clone(),
                    )));
                }
                params.push(CallableParam::new(
                    DbString::Static("iterable"),
                    ParamType::PositionalOrKeyword(new_class!(
                        i_s.db.python_state.iterable_link(),
                        Type::Any(AnyCause::Explicit),
                    )),
                ));
                Arc::new(CallableContent {
                    kind: FunctionKind::Classmethod {
                        had_first_self_or_class_annotation: true,
                    },
                    ..CallableContent::new_simple(
                        Some(DbString::Static("_make")),
                        Some(self.name),
                        PointLink::new(FileIndex(0), 0),
                        i_s.db.python_state.empty_type_var_likes.clone(),
                        CallableParams::new_simple(params.into()),
                        as_self.map(|as_self| as_self()).unwrap_or(Type::Self_),
                    )
                })
            }),
            "_fields" => Type::Tuple(Tuple::new_fixed_length(
                std::iter::repeat_n(i_s.db.python_state.str_type(), self.params().len()).collect(),
            )),
            "_field_defaults" => new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                i_s.db.python_state.str_type(),
                Type::Any(AnyCause::Explicit),
            ),
            "_field_types" => new_class!(
                i_s.db.python_state.dict_node_ref().as_link(),
                i_s.db.python_state.str_type(),
                Type::Any(AnyCause::Explicit),
            ),
            "_source" => i_s.db.python_state.str_type(),
            "__mul__" | "__rmul__" | "__add__" => {
                return lookup_tuple_magic_methods(self.as_tuple(), name);
            }
            "__match_args__"
                if i_s
                    .db
                    .project
                    .settings
                    .python_version_or_default()
                    .at_least_3_dot(10) =>
            {
                Type::Tuple(Tuple::new_fixed_length(
                    self.params()
                        .iter()
                        .map(|p| {
                            Type::Literal(Literal::new(LiteralKind::String(
                                p.name.as_ref().unwrap().clone(),
                            )))
                        })
                        .collect(),
                ))
            }
            _ => {
                if let Some(param) = self.search_param(i_s.db, name) {
                    attr_kind = AttributeKind::Property {
                        setter_type: None,
                        is_final: false,
                        is_abstract: true,
                    };
                    param.type_.expect_positional_type().clone()
                } else {
                    return LookupDetails::none();
                }
            }
        };
        LookupDetails::new(
            Type::Any(AnyCause::Internal), // TODO is this Any ok?
            LookupResult::UnknownName(Inferred::from_type(type_)),
            attr_kind,
        )
    }

    pub fn type_lookup(
        &self,
        i_s: &InferenceState,
        name: &str,
        as_self: Option<&dyn Fn() -> Type>,
    ) -> LookupDetails<'_> {
        // TODO use or_else like in lookups
        self.lookup_internal(i_s, name, true, as_self)
    }

    pub(crate) fn lookup<'a>(
        &self,
        i_s: &'a InferenceState,
        add_issue: &dyn Fn(IssueKind) -> bool,
        name: &str,
        as_self: Option<&dyn Fn() -> Type>,
    ) -> LookupDetails<'a> {
        self.lookup_internal(i_s, name, false, as_self)
            .or_else(move || {
                i_s.db
                    .python_state
                    .typing_named_tuple_class(i_s.db)
                    .instance()
                    .lookup_with_details(i_s, add_issue, name, LookupKind::Normal)
            })
    }
}

impl PartialEq for NamedTuple {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.__new__ == other.__new__
    }
}

impl Hash for NamedTuple {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.__new__.hash(state);
    }
}
