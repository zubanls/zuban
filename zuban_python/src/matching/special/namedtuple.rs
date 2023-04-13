use parsa_python_ast::{
    AssignmentContent, BlockContent, SimpleStmtContent, SimpleStmts, StmtContent,
};

use crate::{
    database::{
        Database, DbType, GenericsList, PointLink, RecursiveAlias, ReplaceSelf, ReplaceTypeVarLike,
        SpecialType, Variance,
    },
    debug,
    file::{use_cached_annotation_type, PythonFile},
    inference_state::InferenceState,
    matching::{FormatData, Match, Matcher, Type},
    node_ref::NodeRef,
    value::{Class, LookupResult, Value},
    ValueKind,
};

struct NamedTupleMember {
    type_: DbType,
    has_default: bool,
}

#[derive(Debug)]
pub struct InheritedNamedTuple {
    class: PointLink,
    generics: Option<GenericsList>,
}

impl InheritedNamedTuple {
    pub fn new(class: PointLink, generics: Option<GenericsList>) -> Self {
        Self { class, generics }
    }

    fn class<'a>(&'a self, db: &'a Database) -> Class<'a> {
        Class::from_db_type(db, self.class, &self.generics)
    }

    fn todo_types<'a>(&'a self, db: &Database) -> Box<[NamedTupleMember]> {
        // TODO performance this is wrong
        let mut vec = vec![];
        let cls = self.class(db);
        let file = cls.node_ref.file;
        match cls.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_named_tuple_types(db, file, &mut vec, simple)
                        }
                        StmtContent::FunctionDef(_) => (),
                        _ => todo!(),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_named_tuple_types(db, file, &mut vec, simple),
        }
        vec.into_boxed_slice()
    }
}

impl SpecialType for InheritedNamedTuple {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        // TODO is this InferenceState instantiation really needed?
        let types = self
            .todo_types(format_data.db)
            .iter()
            .map(|t| t.type_.format(format_data))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "tuple[{types}, fallback={}]",
            self.class(format_data.db).qualified_name(format_data.db)
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
