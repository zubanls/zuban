use std::rc::Rc;

use once_cell::unsync::OnceCell;

use parsa_python_ast::{
    AssignmentContent, BlockContent, SimpleStmtContent, SimpleStmts, StmtContent, Target,
};

use crate::{
    arguments::Arguments,
    database::{
        CallableContent, CallableParam, CallableParams, Database, DbType, GenericsList,
        ParamSpecific, RecursiveAlias, ReplaceSelf, ReplaceTypeVarLike, SpecialType, StringSlice,
        Variance,
    },
    debug,
    diagnostics::IssueType,
    file::{infer_index, use_cached_annotation_type, File, PythonFile},
    getitem::{SliceType, SliceTypeContent},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::{FormatData, Match, Matcher, ResultContext, Type},
    node_ref::NodeRef,
    value::{Class, LookupResult, Module, OnTypeError, Value},
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

#[derive(Debug, PartialEq, Clone)]
pub struct NamedTuple {
    name: StringSlice,
    // Basically __new__
    constructor: OnceCell<Rc<CallableContent>>,
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
            constructor: OnceCell::from(Rc::new(constructor)),
        }
    }

    pub fn initialize_class_members_lazy(&self, i_s: &InferenceState, cls: Class) {
        let mut vec = vec![];
        let file = cls.node_ref.file;
        match cls.node().block().unpack() {
            BlockContent::Indented(stmts) => {
                for stmt in stmts {
                    match stmt.unpack() {
                        StmtContent::SimpleStmts(simple) => {
                            find_stmt_named_tuple_types(i_s.db, file, &mut vec, simple)
                        }
                        StmtContent::FunctionDef(_) => (),
                        _ => NodeRef::new(file, stmt.index())
                            .add_typing_issue(i_s, IssueType::InvalidStmtInNamedTuple),
                    }
                }
            }
            BlockContent::OneLine(simple) => todo!(), //find_stmt_named_tuple_types(db, file, &mut vec, simple),
        }
        let result = self.constructor.set(Rc::new(CallableContent {
            name: Some(self.name),
            class_name: None,
            defined_at: cls.node_ref.as_link(),
            type_vars: cls.use_cached_type_vars(i_s.db).cloned(),
            params: CallableParams::Simple(vec.into_boxed_slice()),
            result_type: DbType::None,
        }));
        debug_assert_eq!(result, Ok(()));
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

    pub fn format_with_name(&self, format_data: &FormatData, name: &str) -> Box<str> {
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
        format!("tuple[{types}, fallback={name}]",).into()
    }
}

impl SpecialType for NamedTuple {
    fn format(&self, format_data: &FormatData) -> Box<str> {
        self.format_with_name(format_data, &self.qualified_name(format_data.db))
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
        if name == "__init__" {
            return LookupResult::UnknownName(Inferred::execute_db_type(
                i_s,
                DbType::Callable(self.constructor.get().unwrap().clone()),
            ));
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

    fn get_item(
        &self,
        i_s: &InferenceState,
        slice_type: &SliceType,
        result_context: &mut ResultContext,
    ) -> Inferred {
        match slice_type.unpack() {
            SliceTypeContent::Simple(simple) => infer_index(i_s, simple, |index| {
                self.params().get(index).map(|p| {
                    Inferred::execute_db_type(
                        i_s,
                        p.param_specific.expect_positional_db_type_as_ref().clone(),
                    )
                })
            }),
            SliceTypeContent::Slice(_) => todo!(),
            SliceTypeContent::Slices(_) => todo!(),
        }
    }

    fn instantiate(
        &self,
        i_s: &InferenceState,
        full_type: &DbType,
        args: &dyn Arguments,
        on_type_error: OnTypeError,
    ) -> DbType {
        debug!("TODO check namedtuple args");
        full_type.clone()
    }

    fn as_named_tuple(&self) -> Option<&Self> {
        Some(self)
    }
}

fn find_stmt_named_tuple_types(
    db: &Database,
    file: &PythonFile,
    vec: &mut Vec<CallableParam>,
    simple_stmts: SimpleStmts,
) {
    for simple in simple_stmts.iter() {
        match simple.unpack() {
            SimpleStmtContent::Assignment(assignment) => match assignment.unpack() {
                AssignmentContent::WithAnnotation(target, annot, default) => match target {
                    Target::Name(name) => {
                        let t = use_cached_annotation_type(db, file, annot).into_db_type(db);
                        vec.push(CallableParam {
                            param_specific: ParamSpecific::PositionalOrKeyword(t),
                            has_default: default.is_some(),
                            name: Some(StringSlice::from_name(file.file_index(), name.name())),
                        })
                    }
                    _ => todo!(),
                },
                _ => todo!(),
            },
            _ => todo!(),
        }
    }
}
