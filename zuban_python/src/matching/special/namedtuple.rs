use once_cell::unsync::OnceCell;

use parsa_python_ast::{AssignmentContent, SimpleStmtContent, SimpleStmts};

use crate::{
    database::{
        CallableContent, CallableParam, CallableParams, Database, DbType, GenericsList,
        RecursiveAlias, ReplaceSelf, ReplaceTypeVarLike, SpecialType, StringSlice, Variance,
    },
    debug,
    file::{use_cached_annotation_type, PythonFile},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, Match, Matcher, Type},
    node_ref::NodeRef,
    value::{LookupResult, Module, Value},
    ValueKind,
};

#[derive(Debug)]
enum NamedTupleGenerics {
    Some(GenericsList),
    None,
    ToBeDefined,
}

struct NamedTupleMember {
    type_: DbType,
    has_default: bool,
}

#[derive(Debug, PartialEq)]
pub struct NamedTuple {
    name: StringSlice,
    // Basically __new__
    constructor: OnceCell<CallableContent>,
}

impl NamedTuple {
    pub fn new(name: StringSlice) -> Self {
        Self {
            constructor: OnceCell::new(),
            name,
        }
    }

    pub fn from_execution(name: StringSlice, constructor: CallableContent) -> Self {
        Self {
            name,
            constructor: OnceCell::from(constructor),
        }
    }

    fn params(&self) -> &[CallableParam] {
        let CallableParams::Simple(params) = &self.constructor.get().unwrap().params else {
            unreachable!();
        };
        params
    }

    fn qualified_name(&self, db: &Database) -> String {
        let file = db.loaded_python_file(self.name.file_index);
        let module = Module::new(db, file).qualified_name(db);
        format!("{module}.{}", self.name(db))
    }
}

impl SpecialType for NamedTuple {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        // TODO is this InferenceState instantiation really needed?
        let CallableParams::Simple(params) = &self.constructor.get().unwrap().params else {
            unreachable!()
        };
        let types = params
            .iter()
            .map(|t| {
                t.param_specific
                    .expect_positional_db_type_as_ref()
                    .format(format_data)
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "tuple[{types}, fallback={}]",
            self.qualified_name(format_data.db)
        )
        .into()
    }

    fn has_any_internal(
        &self,
        i_s: &InferenceState,
        already_checked: &mut Vec<std::rc::Rc<RecursiveAlias>>,
    ) -> bool {
        todo!()
    }

    fn has_self_type(&self) -> bool {
        debug!("TODO namedtuple has_self_type");
        false
    }

    fn replace_type_var_likes_and_self(
        &self,
        db: &Database,
        callable: ReplaceTypeVarLike,
        replace_self: ReplaceSelf,
    ) -> Option<DbType> {
        debug!("TODO namedtuple replace_type_var_likes_and_self");
        None
    }

    fn kind(&self) -> ValueKind {
        ValueKind::Object
    }

    fn name<'a>(&'a self, db: &'a Database) -> &'a str {
        self.name.as_str(db)
    }

    fn lookup_internal(
        &self,
        i_s: &InferenceState,
        node_ref: Option<NodeRef>,
        name: &str,
    ) -> LookupResult {
        for p in self.params() {
            if name == p.name.unwrap().as_str(i_s.db) {
                return LookupResult::UnknownName(Inferred::execute_db_type(
                    i_s,
                    p.param_specific.expect_positional_db_type_as_ref().clone(),
                ));
            }
        }
        todo!()
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

fn find_stmt_named_tuple_types(
    db: &Database,
    file: &PythonFile,
    vec: &mut Vec<NamedTupleMember>,
    simple_stmts: SimpleStmts,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(name, annot, default) => {
                    vec.push(NamedTupleMember {
                        type_: use_cached_annotation_type(db, file, annot).into_db_type(db),
                        has_default: default.is_some(),
                    })
                }
                _ => todo!(),
            },
            _ => todo!(),
        }
    }
}
