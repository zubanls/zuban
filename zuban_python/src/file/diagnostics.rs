use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use parsa_python_ast::*;

use super::{inference::await_, on_argument_type_error};
use crate::{
    arguments::{CombinedArgs, KnownArgs, NoArgs},
    database::{
        ClassKind, ComplexPoint, Database, Locality, OverloadImplementation, Point, PointType,
        Specific,
    },
    debug,
    diagnostics::{Issue, IssueType},
    file::Inference,
    getitem::SliceType,
    inference_state::InferenceState,
    inferred::{infer_class_method, AttributeKind, Inferred},
    matching::{
        matches_params,
        params::{has_overlapping_params, WrappedParamType, WrappedStar},
        FormatData, Generics, LookupKind, LookupResult, Match, Matcher, OnTypeError, Param,
        ResultContext,
    },
    node_ref::NodeRef,
    type_::{
        format_callable_params, AnyCause, CallableContent, CallableParams, ClassGenerics, DbString,
        FunctionKind, FunctionOverload, GenericItem, GenericsList, Literal, LiteralKind, TupleArgs,
        Type, TypeVarLike, Variance,
    },
    type_helpers::{
        is_private, Class, FirstParamProperties, Function, GeneratorType, Instance, LookupDetails,
        TypeOrClass,
    },
};

lazy_static::lazy_static! {
    static ref FORWARD_OP_METHODS: HashSet<&'static str> = HashSet::from([
        "__add__",
        "__sub__",
        "__mul__",
        "__truediv__",
        "__mod__",
        "__divmod__",
        "__floordiv__",
        "__pow__",
        "__matmul__",
        "__and__",
        "__or__",
        "__xor__",
        "__lshift__",
        "__rshift__",
        "__eq__",
        "__ne__",
        "__lt__",
        "__ge__",
        "__gt__",
        "__le__",
    ]);
    static ref REVERSE_OP_METHODS: HashSet<&'static str> = HashSet::from([
        "radd",
        "rsub",
        "rmul",
        "rtruediv",
        "rmod",
        "rdivmod",
        "rfloordiv",
        "rpow",
        "rmatmul",
        "rand",
        "ror",
        "rxor",
        "rlshift",
        "rrshift",
        "eq",
        "ne",
        "lt",
        "ge",
        "gt",
        "le",
    ]);
    pub static ref OVERLAPPING_REVERSE_TO_NORMAL_METHODS: HashMap<&'static str, &'static str> = HashMap::from([
        ("radd", "__add__"),
        ("rsub", "__sub__"),
        ("rmul", "__mul__"),
        ("rtruediv", "__truediv__"),
        ("rmod", "__mod__"),
        ("rdivmod", "__divmod__"),
        ("rfloordiv", "__floordiv__"),
        ("rpow", "__pow__"),
        ("rmatmul", "__matmul__"),
        ("rand", "__and__"),
        ("ror", "__or__"),
        ("rxor", "__xor__"),
        ("rlshift", "__lshift__"),
        ("rrshift", "__rshift__"),
        ("lt", "__gt__"),
        ("ge", "__le__"),
        ("gt", "__lt__"),
        ("le", "__ge__"),
    ]);
    pub static ref INPLACE_TO_NORMAL_METHODS: HashMap<&'static str, &'static str> = HashMap::from([
        ("iadd", "__add__"),
        ("isub", "__sub__"),
        ("imul", "__mul__"),
        ("itruediv", "__truediv__"),
        ("imod", "__mod__"),
        ("ifloordiv", "__floordiv__"),
        ("ipow", "__pow__"),
        ("imatmul", "__matmul__"),
        ("iand", "__and__"),
        ("ior", "__or__"),
        ("ixor", "__xor__"),
        ("ilshift", "__lshift__"),
        ("irshift", "__rshift__"),
    ]);
}

impl<'db> Inference<'db, '_, '_> {
    pub fn calculate_diagnostics(&mut self) {
        self.calc_stmts_diagnostics(self.file.tree.root().iter_stmts(), None, None);
        for complex_point in unsafe { self.file.complex_points.iter() } {
            if let ComplexPoint::NewTypeDefinition(n) = complex_point {
                // Make sure types are calculated and the errors are generated.
                n.type_(self.i_s);
            }
        }

        if let Some(index) = self.file.symbol_table.lookup_symbol("__getattribute__") {
            NodeRef::new(self.file, index)
                .add_issue(self.i_s, IssueType::GetattributeInvalidAtModuleLevel)
        }
        if let Some(index) = self.file.symbol_table.lookup_symbol("__getattr__") {
            let actual = self.infer_name_by_index(index);
            let actual = actual.as_cow_type(self.i_s);
            let Type::Callable(callable) = &self.i_s.db.python_state.valid_getattr_supertype else {
                unreachable!();
            };

            if !Type::Callable(Rc::new(callable.remove_first_param().unwrap()))
                .is_simple_super_type_of(self.i_s, &actual)
                .bool()
            {
                NodeRef::new(self.file, index).add_issue(
                    self.i_s,
                    IssueType::InvalidSpecialMethodSignature {
                        type_: actual.format_short(self.i_s.db),
                        special_method: "__getattr__",
                    },
                )
            }
        }
    }

    fn calc_simple_stmts_diagnostics(
        &mut self,
        simple_stmts: SimpleStmts,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for simple_stmt in simple_stmts.iter() {
            match simple_stmt.unpack() {
                SimpleStmtContent::Assignment(assignment) => {
                    // Check if protocol assignment is invalid
                    if class.is_some_and(|cls| {
                        cls.is_protocol(self.i_s.db)
                            && match assignment.unpack() {
                                AssignmentContent::WithAnnotation(..) => false,
                                AssignmentContent::Normal(mut targets, _) => {
                                    let first_target = targets.next().unwrap();
                                    match first_target {
                                        Target::Name(n)
                                            if targets.next().is_none()
                                                && n.as_code() == "__slots__" =>
                                        {
                                            false
                                        }
                                        _ => self.check_for_type_comment(assignment).is_none(),
                                    }
                                }
                                AssignmentContent::AugAssign(..) => true,
                            }
                    }) {
                        NodeRef::new(self.file, assignment.index()).add_issue(
                            self.i_s,
                            IssueType::ProtocolMembersMustHaveExplicitlyDeclaredTypes,
                        );
                    }

                    self.cache_assignment_nodes(assignment);
                }
                SimpleStmtContent::StarExpressions(star_exprs) => {
                    self.infer_star_expressions(star_exprs, &mut ResultContext::ExpectUnused);
                }
                SimpleStmtContent::ReturnStmt(return_stmt) => {
                    self.calc_return_stmt_diagnostics(func, return_stmt)
                }
                SimpleStmtContent::YieldExpr(yield_expr) => {
                    self.infer_yield_expr(yield_expr, &mut ResultContext::ExpectUnused);
                }
                SimpleStmtContent::RaiseStmt(raise_stmt) => {
                    if let Some((expr, from_expr)) = raise_stmt.unpack() {
                        self.check_valid_raise_type(expr, false);
                        if let Some(from_expr) = from_expr {
                            self.check_valid_raise_type(from_expr, true)
                        }
                    }
                }
                SimpleStmtContent::ImportFrom(import_from) => {
                    if class.is_some() && func.is_none() {
                        NodeRef::new(self.file, simple_stmt.index())
                            .add_issue(self.i_s, IssueType::UnsupportedClassScopedImport);
                    }
                    self.cache_import_from(import_from);
                }
                SimpleStmtContent::ImportName(import_name) => {
                    self.cache_import_name(import_name);
                }
                SimpleStmtContent::PassStmt(x) => {}
                SimpleStmtContent::GlobalStmt(x) => {}
                SimpleStmtContent::NonlocalStmt(x) => {}
                SimpleStmtContent::AssertStmt(assert_stmt) => {
                    let (expr, message_expr) = assert_stmt.unpack();
                    self.infer_expression(expr);
                    if let Some(message_expr) = message_expr {
                        self.infer_expression(message_expr);
                    }
                }
                SimpleStmtContent::BreakStmt(x) => {}
                SimpleStmtContent::ContinueStmt(x) => {}
                SimpleStmtContent::DelStmt(d) => {
                    self.calc_del_stmt_diagnostics(d.target());
                }
            }
        }
    }

    fn check_valid_raise_type(&mut self, expr: Expression, allow_none: bool) {
        if !valid_raise_type(
            self.i_s,
            NodeRef::new(self.file, expr.index()),
            &self.infer_expression(expr).as_cow_type(self.i_s),
            allow_none,
        ) {
            NodeRef::new(self.file, expr.index())
                .add_issue(self.i_s, IssueType::BaseExceptionExpectedForRaise);
        }
    }

    fn calc_stmts_diagnostics(
        &mut self,
        stmts: StmtIterator,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        // TODO In general all {} blocks are todos
        for stmt in stmts {
            let StmtOrError::Stmt(stmt) = stmt else {
                continue
            };
            let point = self.file.points.get(stmt.index());
            if point.calculated() {
                debug_assert_eq!(point.type_(), PointType::NodeAnalysis);
                continue;
            }

            match stmt.unpack() {
                StmtContent::SimpleStmts(simple_stmts) => {
                    self.calc_simple_stmts_diagnostics(simple_stmts, class, func)
                }
                StmtContent::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                StmtContent::ClassDef(class) => self.calc_class_diagnostics(class),
                StmtContent::Decorated(decorated) => match decorated.decoratee() {
                    Decoratee::FunctionDef(f) => self.calc_function_diagnostics(f, class),
                    Decoratee::ClassDef(class) => self.calc_class_diagnostics(class),
                    Decoratee::AsyncFunctionDef(func) => {
                        self.calc_function_diagnostics(func, class)
                    }
                },
                StmtContent::IfStmt(if_stmt) => {
                    for block in if_stmt.iter_blocks() {
                        match block {
                            IfBlockType::If(if_expr, block) => {
                                self.infer_named_expression(if_expr);
                                self.calc_block_diagnostics(block, class, func)
                            }
                            IfBlockType::Else(block) => {
                                self.calc_block_diagnostics(block, class, func)
                            }
                        }
                    }
                }
                StmtContent::ForStmt(for_stmt) => {
                    self.calc_for_stmt_diagnostics(for_stmt, class, func, false)
                }
                StmtContent::TryStmt(try_stmt) => {
                    self.calc_try_stmt_diagnostics(try_stmt, class, func)
                }
                StmtContent::WhileStmt(while_stmt) => {
                    let (condition, block, else_block) = while_stmt.unpack();
                    self.infer_named_expression(condition);
                    self.calc_block_diagnostics(block, class, func);
                    if let Some(else_block) = else_block {
                        self.calc_block_diagnostics(else_block.block(), class, func)
                    }
                }
                StmtContent::WithStmt(with_stmt) => {
                    self.calc_with_stmt(with_stmt, class, func, false)
                }
                StmtContent::MatchStmt(match_stmt) => {
                    debug!("TODO match_stmt diagnostics");
                }
                StmtContent::AsyncStmt(async_stmt) => match async_stmt.unpack() {
                    AsyncStmtContent::FunctionDef(func) => {
                        self.calc_function_diagnostics(func, class)
                    }
                    AsyncStmtContent::ForStmt(for_stmt) => {
                        self.calc_for_stmt_diagnostics(for_stmt, class, func, true)
                    }
                    AsyncStmtContent::WithStmt(with_stmt) => {
                        self.calc_with_stmt(with_stmt, class, func, true)
                    }
                },
                StmtContent::Newline => {}
            };
            self.file
                .points
                .set(stmt.index(), Point::new_node_analysis(Locality::Todo));
        }
    }

    fn calc_with_stmt(
        &mut self,
        with_stmt: WithStmt,
        class: Option<Class>,
        func: Option<&Function>,
        is_async: bool,
    ) {
        let (with_items, block) = with_stmt.unpack();
        for with_item in with_items.iter() {
            let (expr, target) = with_item.unpack();
            let from = NodeRef::new(self.file, expr.index());
            let result = self.infer_expression(expr);
            let mut enter_result = result.type_lookup_and_execute_with_attribute_error(
                self.i_s,
                from,
                match is_async {
                    false => "__enter__",
                    true => "__aenter__",
                },
                &NoArgs::new(from),
            );
            if is_async {
                enter_result = await_(
                    self.i_s,
                    enter_result,
                    from,
                    r#""async with" for "__aenter__""#,
                    false,
                );
            }
            let exit_result = result.type_lookup_and_execute_with_attribute_error(
                self.i_s,
                from,
                match is_async {
                    false => "__exit__",
                    true => "__aexit__",
                },
                &CombinedArgs::new(
                    &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                    &CombinedArgs::new(
                        // TODO don't use any here.
                        &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                        &KnownArgs::new(&Inferred::new_any(AnyCause::Todo), from),
                    ),
                ),
            );
            if is_async {
                await_(
                    self.i_s,
                    exit_result,
                    from,
                    r#""async with" for "__aexit__""#,
                    false,
                );
            }
            if let Some(target) = target {
                self.assign_targets(
                    target,
                    enter_result,
                    NodeRef::new(self.file, with_item.index()),
                    true,
                )
            }
        }
        self.calc_block_diagnostics(block, class, func);
    }

    fn calc_untyped_block_diagnostics(&mut self, block: Block) {
        for interesting in block.search_relevant_untyped_nodes() {
            match interesting {
                RelevantUntypedNode::Primary(p) => {
                    let PrimaryOrAtom::Atom(atom) = p.first() else {
                        continue
                    };
                    let AtomContent::Name(n) = atom.unpack() else {
                        continue
                    };
                    if n.as_code() == "reveal_type" && !self.file.points.get(n.index()).calculated()
                    {
                        let PrimaryContent::Execution(_) = p.second() else {
                            continue
                        };
                        let n = NodeRef::new(self.file, p.index());
                        n.add_issue(self.i_s, IssueType::Note("Revealed type is \"Any\"".into()));
                        n.add_issue(
                            self.i_s,
                            IssueType::Note(
                                "'reveal_type' always outputs 'Any' in unchecked functions".into(),
                            ),
                        );
                    }
                }
                RelevantUntypedNode::Assignment(a) => {
                    let is_type_definition = match a.unpack() {
                        AssignmentContent::Normal(_, right) => {
                            self.check_for_type_comment(a).is_some()
                        }
                        AssignmentContent::WithAnnotation(_, annotation, _) => true,
                        AssignmentContent::AugAssign(..) => false,
                    };
                    if is_type_definition {
                        NodeRef::new(self.file, a.index())
                            .add_issue(self.i_s, IssueType::AnnotationInUntypedFunction);
                    }
                }
                RelevantUntypedNode::ImportFrom(i) => self.cache_import_from(i),
                RelevantUntypedNode::ImportName(i) => self.cache_import_name(i),
                RelevantUntypedNode::FunctionDef(func) => {
                    // TODO
                }
                RelevantUntypedNode::ClassDef(class) => {
                    // TODO
                }
            }
        }
    }

    pub fn calc_block_diagnostics(
        &mut self,
        block: Block,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        match block.unpack() {
            BlockContent::Indented(stmts) => self.calc_stmts_diagnostics(stmts, class, func),
            BlockContent::OneLine(simple_stmts) => {
                self.calc_simple_stmts_diagnostics(simple_stmts, class, func)
            }
        }
    }

    fn calc_class_diagnostics(&mut self, class: ClassDef) {
        let (arguments, block) = class.unpack();
        let name_def = NodeRef::new(self.file, class.name_definition().index());
        debug!("TODO this from is completely wrong and should never be used.");
        let hack = name_def;
        self.cache_class(name_def, class);
        let class_node_ref = NodeRef::new(self.file, class.index());
        let db = self.i_s.db;
        let c = Class::with_self_generics(db, class_node_ref);
        let class_infos = c.use_cached_class_infos(db);
        if matches!(class_infos.class_kind, ClassKind::TypedDict) {
            // TypedDicts are special, because they really only contain annotations and no methods.
            // We skip all of this logic, because there's custom logic for TypedDicts.
            return;
        }
        let i_s = self.i_s.with_diagnostic_class_context(&c);
        let mut inference = self.file.inference(&i_s);
        inference.calc_block_diagnostics(block, Some(c), None);

        for (i, base1) in c.bases(db).enumerate() {
            let cls1 = match base1 {
                TypeOrClass::Class(c) => c,
                TypeOrClass::Type(t) => {
                    debug!("TODO check complex base types");
                    continue;
                }
            };
            for (type_var_like, arg) in cls1
                .use_cached_type_vars(i_s.db)
                .iter()
                .zip(cls1.type_var_remap.map(|g| g.iter()).unwrap_or([].iter()))
            {
                if let GenericItem::TypeArg(Type::TypeVar(tv)) = arg {
                    if let TypeVarLike::TypeVar(tv_def) = type_var_like {
                        if tv.type_var.variance != Variance::Invariant
                            && tv.type_var.variance != tv_def.variance
                        {
                            NodeRef::new(self.file, arguments.unwrap().index()).add_issue(
                                &i_s,
                                IssueType::TypeVarVarianceIncompatibleWithParentType {
                                    type_var_name: tv.type_var.name(i_s.db).into(),
                                },
                            );
                        }
                    }
                }
            }
            let instance1 = Instance::new(cls1, None);
            for base2 in c.bases(db).skip(i + 1) {
                let instance2 = match base2 {
                    TypeOrClass::Class(c) => Instance::new(c, None),
                    TypeOrClass::Type(t) => continue,
                };
                instance1.run_on_symbols(|name| {
                    if name.starts_with("__") {
                        return;
                    }
                    if let Some(inf) = instance2.full_lookup(self.i_s, hack, name).into_maybe_inferred()
                    {
                        if c.lookup_symbol(self.i_s, name).into_maybe_inferred().is_some() {
                            // These checks happen elsewhere.
                            debug!("TODO this check might omit the check between current class and c2?");
                            return
                        }
                        let second = inf.as_cow_type(self.i_s);
                        let first = instance1.full_lookup(self.i_s, hack, name).into_inferred();
                        let first = first.as_cow_type(self.i_s);
                        if !first
                            .is_sub_type_of(
                                self.i_s,
                                &mut Matcher::new_class_matcher(self.i_s, c).with_ignore_positional_param_names(),
                                &second,
                            )
                            .bool()
                        {
                            let index =
                                c.node().arguments().unwrap().iter().nth(i).unwrap().index();
                            NodeRef::new(self.file, index).add_issue(
                                self.i_s,
                                IssueType::MultipleInheritanceIncompatibility {
                                    name: name.into(),
                                    class1: base1.name(db).into(),
                                    class2: base2.name(db).into(),
                                },
                            );
                        }
                    }
                });
            }
        }
        for table in [
            &c.class_storage.class_symbol_table,
            &c.class_storage.self_symbol_table,
        ] {
            for (name, index) in unsafe { table.iter_on_finished_table() } {
                if ["__init__", "__new__", "__init_subclass__", "__slots__"].contains(&name)
                    || is_private(name)
                {
                    continue;
                }
                let mut node_ref = NodeRef::new(self.file, *index - NAME_DEF_TO_NAME_DIFFERENCE);
                if name == "__post_init__" {
                    if let Some(dataclass) = c.maybe_dataclass() {
                        let override_details = Instance::new(c, None).lookup_on_self(
                            self.i_s,
                            &|issue| todo!(),
                            name,
                            LookupKind::OnlyType,
                        );
                        let __post_init__ = dataclass.expect_calculated_post_init();
                        let original_details = LookupDetails {
                            class: TypeOrClass::Type(Cow::Owned(Type::Dataclass(
                                dataclass.clone(),
                            ))),
                            lookup: LookupResult::UnknownName(Inferred::from_type(Type::Callable(
                                Rc::new(__post_init__.clone()),
                            ))),
                            attr_kind: AttributeKind::DefMethod,
                        };
                        check_override(
                            &i_s,
                            node_ref,
                            original_details,
                            override_details,
                            name,
                            |_, _| "dataclass",
                            Some(&|| {
                                let params = format_callable_params(
                                    &FormatData::new_short(i_s.db),
                                    None,
                                    false,
                                    __post_init__.expect_simple_params().iter(),
                                    false,
                                );
                                format!("def __post_init__(self, {params}) -> None")
                            }),
                        );
                        continue;
                    }
                }

                // Calculate if there is an @override decorator
                let mut has_override_decorator = false;
                if let Some(func_def) = NodeRef::new(self.file, *index).maybe_name_of_function() {
                    if !func_def.is_typed() {
                        // Mypy completely ignores untyped functions.
                        continue;
                    }
                    if let Some(decorated) = func_def.maybe_decorated() {
                        let decorators = decorated.decorators();
                        for decorator in decorators.iter() {
                            if let Some(redirect) =
                                NodeRef::new(self.file, decorator.index()).maybe_redirect(db)
                            {
                                if redirect == db.python_state.typing_override() {
                                    has_override_decorator = true;
                                }
                                if redirect == db.python_state.typing_overload() {
                                    // In Mypy the error is on the first decorator of an @overload.
                                    node_ref = NodeRef::new(
                                        self.file,
                                        decorators
                                            .iter()
                                            .next()
                                            .unwrap()
                                            .named_expression()
                                            .index(),
                                    );
                                }
                            }
                        }
                    }
                }

                find_and_check_override(self.i_s, node_ref, c, name, has_override_decorator)
            }
        }
        if let Some(node_index) = c
            .class_storage
            .class_symbol_table
            .lookup_symbol("__slots__")
        {
            let inf = self.infer_name_by_index(node_index);
            let t = inf.as_cow_type(&i_s);
            if !t
                .is_simple_sub_type_of(&i_s, &i_s.db.python_state.iterable_of_str)
                .bool()
            {
                NodeRef::new(self.file, node_index).add_issue(
                    &i_s,
                    IssueType::InvalidSlotsDefinition {
                        actual: t.format_short(i_s.db),
                    },
                )
            }
        }
        if matches!(class_infos.class_kind, ClassKind::Protocol) {
            for (name, name_index) in
                unsafe { c.class_storage.self_symbol_table.iter_on_finished_table() }
            {
                if c.class_storage
                    .class_symbol_table
                    .lookup_symbol(name)
                    .is_none()
                {
                    let from = NodeRef::new(self.file, *name_index);
                    // Apparently Mypy raises two issues here.
                    from.add_issue(
                        self.i_s,
                        IssueType::ProtocolMembersCannotHaveSelfVariableDefinitions,
                    );
                    from.add_issue(
                        self.i_s,
                        IssueType::AttributeError {
                            object: format!("\"{}\"", c.name()).into(),
                            name: name.into(),
                        },
                    )
                }
            }
            check_protocol_type_var_variances(self.i_s, c)
        }
    }

    fn calc_function_diagnostics(&mut self, f: FunctionDef, class: Option<Class>) {
        let i_s = self.i_s;
        let function = Function::new(NodeRef::new(self.file, f.index()), class);
        let decorator_ref = function.decorator_ref();
        let mut is_overload_member = false;
        let inf = function.as_inferred_from_name(i_s);
        if let Some(ComplexPoint::FunctionOverload(o)) = decorator_ref.complex() {
            is_overload_member = true;
            for (i, c1) in o.iter_functions().enumerate() {
                if let Some(implementation) = &o.implementation {
                    self.calc_overload_implementation_diagnostics(c1, implementation, i + 1)
                }
                for (k, c2) in o.iter_functions().skip(i + 1).enumerate() {
                    if is_overload_unmatchable(i_s, c1, c2) {
                        NodeRef::from_link(i_s.db, c2.defined_at).add_issue(
                            i_s,
                            IssueType::OverloadUnmatchable {
                                matchable_signature_index: i + 1,
                                unmatchable_signature_index: i + k + 2,
                            },
                        );
                    } else if !c1
                        .return_type
                        .is_simple_sub_type_of(i_s, &c2.return_type)
                        .bool()
                        && has_overlapping_params(i_s, &c1.params, &c2.params)
                    {
                        NodeRef::from_link(i_s.db, c1.defined_at).add_issue(
                            i_s,
                            IssueType::OverloadIncompatibleReturnTypes {
                                first_signature_index: i + 1,
                                second_signature_index: i + k + 2,
                            },
                        );
                    }
                }
            }
        } else if function.node_ref.point().maybe_specific() == Some(Specific::DecoratedFunction)
            && decorator_ref.point().maybe_specific() == Some(Specific::OverloadUnreachable)
        {
            is_overload_member = true;
        }
        if class.is_some()
            && function.node().params().iter().next().is_none()
            && function.kind(i_s) != FunctionKind::Staticmethod
        {
            function
                .node_ref
                .add_issue(i_s, IssueType::MethodWithoutArguments)
        }

        // Make sure the type vars are properly pre-calculated
        function.type_vars(i_s);
        let (name, params, return_annotation, block) = f.unpack();
        if !is_overload_member {
            // Check defaults here.
            for param in params.iter() {
                if let Some(annotation) = param.annotation() {
                    if let Some(default) = param.default() {
                        let t = self.use_cached_param_annotation_type(annotation);
                        let inf = self
                            .infer_expression_with_context(default, &mut ResultContext::Known(&t));
                        t.error_if_not_matches(
                            i_s,
                            &inf,
                            |issue| NodeRef::new(self.file, default.index()).add_issue(i_s, issue),
                            |got, expected| {
                                if self.file.is_stub_or_in_protocol(i_s)
                                    && default.is_ellipsis_literal()
                                {
                                    // In stubs it is allowed to do stuff like:
                                    // def foo(x: int = ...) -> int: ...
                                    return None;
                                }
                                Some(IssueType::IncompatibleDefaultArgument {
                                    argument_name: Box::from(param.name_definition().as_code()),
                                    got,
                                    expected,
                                })
                            },
                        );
                    }
                }
            }
        }
        let flags = &i_s.db.project.flags;
        let mut had_missing_annotation = false;
        for param in params
            .iter()
            .skip((class.is_some() && function.kind(i_s) != FunctionKind::Staticmethod).into())
        {
            if let Some(annotation) = param.annotation() {
                let t = self.use_cached_param_annotation_type(annotation);
                if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == Variance::Covariant)
                {
                    if !["__init__", "__new__", "__post_init__"].contains(&name.as_code()) {
                        NodeRef::new(self.file, annotation.index())
                            .add_issue(i_s, IssueType::TypeVarCovariantInParamType);
                    }
                }

                if param.kind() == ParamKind::StarStar {
                    if let Type::TypedDict(td) = t.as_ref() {
                        let mut overlapping_names = vec![];
                        for member in td.members(i_s.db) {
                            for p in params.iter() {
                                let name = member.name.as_str(i_s.db);
                                if matches!(
                                    p.kind(),
                                    ParamKind::PositionalOrKeyword | ParamKind::KeywordOnly
                                ) && name == p.name_definition().as_code()
                                {
                                    overlapping_names.push(format!("\"{name}\""));
                                    break;
                                }
                            }
                        }
                        if !overlapping_names.is_empty() {
                            function.add_issue_for_declaration(
                                i_s,
                                IssueType::TypedDictArgumentNameOverlapWithUnpack {
                                    names: overlapping_names.join(", ").into(),
                                },
                            );
                        }
                    }
                }
            } else if flags.disallow_incomplete_defs {
                had_missing_annotation = true;
            }
        }
        if had_missing_annotation {
            function
                .node_ref
                .add_issue(i_s, IssueType::FunctionMissingParamAnnotations);
        }

        if let Some(return_annotation) = return_annotation {
            let t = self.use_cached_return_annotation_type(return_annotation);
            if matches!(t.as_ref(), Type::TypeVar(tv) if tv.type_var.variance == Variance::Contravariant)
            {
                NodeRef::new(self.file, return_annotation.index())
                    .add_issue(i_s, IssueType::TypeVarContravariantInReturnType);
            }
            if function.is_generator() {
                let expected = if function.is_async() {
                    &i_s.db.python_state.async_generator_with_any_generics
                } else {
                    &i_s.db.python_state.generator_with_any_generics
                };
                if !t.is_simple_super_type_of(i_s, &expected).bool() {
                    if function.is_async() {
                        NodeRef::new(self.file, return_annotation.index())
                            .add_issue(i_s, IssueType::InvalidAsyncGeneratorReturnType);
                    } else {
                        NodeRef::new(self.file, return_annotation.index())
                            .add_issue(i_s, IssueType::InvalidGeneratorReturnType);
                    }
                }
            }
        } else if flags.disallow_incomplete_defs {
            function
                .node_ref
                .add_issue(i_s, IssueType::FunctionMissingReturnAnnotation);
        }

        let is_dynamic = function.is_dynamic();
        let args = NoArgs::new(NodeRef::new(self.file, f.index()));
        let function_i_s = &mut i_s.with_diagnostic_func_and_args(&function, &args);
        let mut inference = self.file.inference(function_i_s);
        if !is_dynamic || flags.check_untyped_defs {
            inference.calc_block_diagnostics(block, None, Some(&function))
        } else {
            inference.calc_untyped_block_diagnostics(block)
        }
        if flags.disallow_untyped_defs && !flags.disallow_incomplete_defs {
            match (
                function.is_missing_param_annotations(i_s),
                function.return_annotation().is_none(),
            ) {
                (true, true) => {
                    function.add_issue_for_declaration(i_s, IssueType::FunctionIsDynamic)
                }
                (true, false) => function
                    .add_issue_for_declaration(i_s, IssueType::FunctionMissingParamAnnotations),
                (false, true) => function
                    .add_issue_for_declaration(i_s, IssueType::FunctionMissingReturnAnnotation),
                (false, false) => (),
            }
        }

        if function.is_dunder_new() {
            let mut class = class.unwrap();
            // Here we do not want self generics, we actually want Any generics.
            class.generics = Generics::NotDefinedYet;
            let Some(callable) = infer_class_method(
                i_s,
                class,
                class,
                &function.as_callable(i_s, FirstParamProperties::None),
            ) else {
                todo!()
            };
            match &callable.return_type {
                Type::Class(_) => {
                    let t = &callable.return_type;
                    if !class.as_type(i_s.db).is_simple_super_type_of(i_s, t).bool() {
                        function.expect_return_annotation_node_ref().add_issue(
                            i_s,
                            IssueType::NewIncompatibleReturnType {
                                returns: t.format_short(i_s.db),
                                must_return: class.format_short(i_s.db),
                            },
                        )
                    }
                }
                Type::Type(_) => (),
                Type::Any(_) => (),
                Type::Enum(e) if e.class == class.node_ref.as_link() => (),
                t => function.expect_return_annotation_node_ref().add_issue(
                    i_s,
                    IssueType::NewMustReturnAnInstance {
                        got: t.format_short(i_s.db),
                    },
                ),
            }
        }

        if flags.disallow_any_unimported {
            for param in params
                .iter()
                .skip((class.is_some() && function.kind(i_s) != FunctionKind::Staticmethod).into())
            {
                if let Some(annotation) = param.annotation() {
                    let t = self.use_cached_param_annotation_type(annotation);
                    // TODO implement --disallow-any-unimported
                }
            }
        }

        if let Some(magic_name) = name
            .as_code()
            .strip_prefix("__")
            .and_then(|n| n.strip_suffix("__"))
        {
            if class.is_some() {
                match magic_name {
                    "init" | "init_subclass" => {
                        if let Some(return_annotation) = function.return_annotation() {
                            if !matches!(function.return_type(i_s).as_ref(), Type::None) {
                                // __init__ and __init_subclass__ must return None
                                NodeRef::new(self.file, return_annotation.expression().index())
                                    .add_issue(
                                        i_s,
                                        IssueType::MustReturnNone {
                                            function_name: function.name().into(),
                                        },
                                    )
                            }
                        }
                    }
                    "exit" => {
                        // Check the return type of __exit__
                        self.check_magic_exit(function)
                    }
                    "getattr" => {
                        let func_type = function.as_type(self.i_s, FirstParamProperties::None);
                        if !self
                            .i_s
                            .db
                            .python_state
                            .valid_getattr_supertype
                            .clone()
                            .is_simple_super_type_of(self.i_s, &func_type)
                            .bool()
                        {
                            function.add_issue_for_declaration(
                                self.i_s,
                                IssueType::InvalidSpecialMethodSignature {
                                    type_: func_type.format_short(self.i_s.db),
                                    special_method: "__getattr__",
                                },
                            )
                        }
                    }
                    _ => {
                        // Check reverse magic methods like __rmul__
                        self.check_overlapping_op_methods(function, magic_name);
                        self.check_inplace_methods(function, magic_name);
                    }
                }
            }
        }
    }

    fn calc_overload_implementation_diagnostics(
        &mut self,
        overload_item: &CallableContent,
        implementation: &OverloadImplementation,
        signature_index: usize,
    ) {
        let matcher = &mut Matcher::new_reverse_callable_matcher(&implementation.callable);
        let implementation_result = &implementation.callable.return_type;
        let item_result = &overload_item.return_type;
        // This is bivariant matching. This is how Mypy allows subtyping.
        if !item_result
            .is_sub_type_of(self.i_s, matcher, implementation_result)
            .bool()
            && !item_result
                .is_super_type_of(self.i_s, matcher, implementation_result)
                .bool()
        {
            implementation
                .function(self.i_s.db, None)
                .add_issue_onto_start_including_decorator(
                    self.i_s,
                    IssueType::OverloadImplementationReturnTypeIncomplete { signature_index },
                );
        }

        let match_ = matches_params(
            self.i_s,
            matcher,
            &overload_item.params,
            &implementation.callable.params,
        );
        if !match_.bool() {
            implementation
                .function(self.i_s.db, None)
                .add_issue_onto_start_including_decorator(
                    self.i_s,
                    IssueType::OverloadImplementationArgumentsNotBroadEnough { signature_index },
                );
        }
    }

    fn calc_return_stmt_diagnostics(&mut self, func: Option<&Function>, return_stmt: ReturnStmt) {
        if let Some(func) = func {
            if let Some(annotation) = func.return_annotation() {
                let i_s = self.i_s;
                if let Some(star_expressions) = return_stmt.star_expressions() {
                    let mut t = self.use_cached_return_annotation_type(annotation);
                    if func.is_generator() {
                        if func.is_async() {
                            NodeRef::new(self.file, star_expressions.index())
                                .add_issue(i_s, IssueType::ReturnInAsyncGenerator);
                            return;
                        } else {
                            t = Cow::Owned(
                                GeneratorType::from_type(i_s.db, t)
                                    .map(|g| g.return_type.unwrap_or(Type::None))
                                    .unwrap_or(Type::Any(AnyCause::Todo)),
                            );
                        }
                    }
                    let inf = self
                        .infer_star_expressions(star_expressions, &mut ResultContext::Known(&t));
                    if i_s.db.project.flags.warn_return_any
                        && matches!(inf.as_cow_type(i_s).as_ref(), Type::Any(_))
                        && t.as_ref() != &i_s.db.python_state.object_type()
                        && !t
                            .iter_with_unpacked_unions()
                            .any(|t| matches!(t, Type::Any(_)))
                    {
                        NodeRef::new(self.file, star_expressions.index()).add_issue(
                            i_s,
                            IssueType::ReturnedAnyWarning {
                                expected: t.format_short(i_s.db),
                            },
                        )
                    }
                    t.error_if_not_matches(
                        i_s,
                        &inf,
                        |issue| {
                            NodeRef::new(self.file, star_expressions.index()).add_issue(i_s, issue)
                        },
                        |got, expected| Some(IssueType::IncompatibleReturn { got, expected }),
                    );
                } else {
                    debug!("TODO what about an implicit None?");
                }
            } else {
                if let Some(star_expressions) = return_stmt.star_expressions() {
                    self.infer_star_expressions(star_expressions, &mut ResultContext::Unknown);
                }
            }
        }
    }

    pub fn cache_for_stmt_names(
        &mut self,
        star_targets: StarTargets,
        star_exprs: StarExpressions,
        is_async: bool,
    ) {
        let star_targets_point = self.file.points.get(star_targets.index());
        if star_targets_point.calculated() {
            debug_assert_eq!(star_targets_point.type_(), PointType::NodeAnalysis);
            return;
        }
        let inf = self.infer_star_expressions(star_exprs, &mut ResultContext::Unknown);
        let from = NodeRef::new(self.file, star_exprs.index());
        let element = if is_async {
            await_aiter_and_next(self.i_s, inf, from)
        } else {
            inf.iter(self.i_s, NodeRef::new(self.file, star_exprs.index()))
                .infer_all(self.i_s)
        };
        debug!("For loop input: {}", element.format_short(self.i_s));
        self.assign_targets(star_targets.as_target(), element, from, false);
        self.file.points.set(
            star_targets.index(),
            Point::new_node_analysis(Locality::Todo),
        );
    }

    fn calc_for_stmt_diagnostics(
        &mut self,
        for_stmt: ForStmt,
        class: Option<Class>,
        func: Option<&Function>,
        is_async: bool,
    ) {
        let (star_targets, star_exprs, block, else_block) = for_stmt.unpack();
        self.cache_for_stmt_names(star_targets, star_exprs, is_async);
        self.calc_block_diagnostics(block, class, func);
        if let Some(else_block) = else_block {
            self.calc_block_diagnostics(else_block.block(), class, func);
        }
    }

    fn calc_try_stmt_diagnostics(
        &mut self,
        try_stmt: TryStmt,
        class: Option<Class>,
        func: Option<&Function>,
    ) {
        for b in try_stmt.iter_blocks() {
            match b {
                TryBlockType::Try(block) => self.calc_block_diagnostics(block, class, func),
                TryBlockType::Except(b) => {
                    let (except_expression, block) = b.unpack();
                    if let Some(except_expression) = except_expression {
                        let expression = except_expression.expression();
                        let inf = self.infer_expression(expression);
                        if !matches!(
                            except_type(self.i_s, &inf.as_cow_type(self.i_s), true),
                            ExceptType::ContainsOnlyBaseExceptions
                        ) {
                            NodeRef::new(self.file, expression.index())
                                .add_issue(self.i_s, IssueType::BaseExceptionExpected);
                        }
                    }
                    self.calc_block_diagnostics(block, class, func)
                }
                TryBlockType::ExceptStar(except_star) => {
                    let (except_expression, block) = except_star.unpack();
                    let expression = except_expression.expression();
                    let inf = self.infer_expression(expression);
                    match except_type(self.i_s, &inf.as_cow_type(self.i_s), true) {
                        ExceptType::ContainsOnlyBaseExceptions => (),
                        ExceptType::HasExceptionGroup => {
                            NodeRef::new(self.file, expression.index()).add_issue(
                                self.i_s,
                                IssueType::ExceptStarIsNotAllowedToBeAnExceptionGroup,
                            );
                        }
                        ExceptType::Invalid => {
                            NodeRef::new(self.file, expression.index())
                                .add_issue(self.i_s, IssueType::BaseExceptionExpected);
                        }
                    }
                    self.calc_block_diagnostics(block, class, func)
                }
                TryBlockType::Else(b) => self.calc_block_diagnostics(b.block(), class, func),
                TryBlockType::Finally(b) => self.calc_block_diagnostics(b.block(), class, func),
            }
        }
    }

    pub fn calc_fstring_diagnostics(&mut self, fstring: FString) {
        self.calc_fstring_content_diagnostics(fstring.iter_content())
    }

    fn calc_fstring_content_diagnostics<'x>(
        &mut self,
        iter: impl Iterator<Item = FStringContent<'x>>,
    ) {
        for content in iter {
            match content {
                FStringContent::FStringExpr(e) => {
                    let (expressions, spec) = e.unpack();
                    self.infer_star_expressions(expressions, &mut ResultContext::Unknown);
                    if let Some(spec) = spec {
                        self.calc_fstring_content_diagnostics(spec.iter_content());
                    }
                }
                FStringContent::FStringString(_) => (),
            }
        }
    }

    fn calc_del_stmt_diagnostics(&mut self, target: Target) {
        match target {
            Target::Name(name_def) => debug!("TODO del name"),
            Target::NameExpression(primary_target, name_def) => {
                // TODO this should still be implemented
                //self.infer_single_target(target);
                let node_ref = NodeRef::new(self.file, name_def.index());
                // We do a normal lookup to check that the attribute is there.
                self.infer_primary_target_or_atom(primary_target.first())
                    .lookup(self.i_s, node_ref, name_def.as_code(), LookupKind::Normal);
            }
            Target::IndexExpression(primary_target) => {
                let base = self.infer_primary_target_or_atom(primary_target.first());
                let PrimaryContent::GetItem(s) = primary_target.second() else {
                    unreachable!()
                };
                let slice_type = SliceType::new(self.file, primary_target.index(), s);
                let node_ref = slice_type.as_node_ref();
                base.lookup(self.i_s, node_ref, "__delitem__", LookupKind::OnlyType)
                    .into_inferred()
                    .execute_with_details(
                        self.i_s,
                        &slice_type.as_args(*self.i_s),
                        &mut ResultContext::ExpectUnused,
                        OnTypeError::new(&on_argument_type_error),
                    );
            }
            Target::Tuple(targets) => {
                for target in targets {
                    self.calc_del_stmt_diagnostics(target)
                }
            }
            Target::Starred(_) => unreachable!(),
        }
    }

    fn check_overlapping_op_methods(&self, func: Function, short_reverse_name: &str) {
        let i_s = self.i_s;
        let Some(normal_magic) = OVERLAPPING_REVERSE_TO_NORMAL_METHODS.get(short_reverse_name) else {
            return
        };

        let invalid_signature = || {
            func.add_issue_for_declaration(
                i_s,
                IssueType::InvalidSignature {
                    signature: func
                        .as_type(i_s, FirstParamProperties::None)
                        .format_short(i_s.db),
                },
            )
        };

        let from = func.node_ref; // TODO this NodeRef shouldn't be used.
        let mut param_iterator = func.iter_params();
        let first_param = param_iterator.next();
        let Some(param) = param_iterator.next().or_else(|| {
            first_param.filter(|first_param| {
                first_param.kind(i_s.db) == ParamKind::Star
            })
        }) else {
            // If there is param, the signature is invalid and should be checked elsewhere.
            return invalid_signature()
        };
        if param_iterator.any(|param| !param.has_default_or_stars(i_s.db)) {
            return invalid_signature();
        }
        let forward_type = match param.specific(i_s.db) {
            WrappedParamType::PositionalOnly(t)
            | WrappedParamType::PositionalOrKeyword(t)
            | WrappedParamType::Star(WrappedStar::ArbitraryLen(t)) => t,
            _ => return invalid_signature(),
        };
        let Some(forward_type) = forward_type else {
            return  // If the type is Any, we do not need to check.
        };
        forward_type.run_after_lookup_on_each_union_member(
            i_s,
            None,
            from.file_index(),
            normal_magic,
            LookupKind::OnlyType,
            &mut ResultContext::Unknown,
            &|issue| todo!(),
            &mut |forward, lookup_details| {
                let check = |callable: &CallableContent| {
                    // Can only overlap if the classes differ. On the same class __radd__ will
                    // never be called if there's a __add__ as well, because in that case __add__
                    // will be preferred.
                    let reverse = func.class.unwrap().as_type(i_s.db);
                    if forward.is_simple_same_type(i_s, &reverse).bool() {
                        return;
                    }

                    // The params must cycle for it to be an unsafe overlap.
                    let Some(reverse_param_type) = callable.first_positional_type() else {
                        // If there is no positional type, the signature is invalid and should be
                        // checked elsewhere.
                        return
                    };
                    if !reverse
                        .is_simple_sub_type_of(i_s, &reverse_param_type)
                        .bool()
                        && !reverse
                            .is_simple_super_type_of(i_s, &reverse_param_type)
                            .bool()
                    {
                        return;
                    }

                    // I'm not 100% sure why this variance calculation is necessary, but I believe
                    // it's because Python calls the reverse methods before the normal methods when
                    // the right type is a subtype of the left.
                    let variance = match reverse.is_simple_sub_type_of(i_s, forward).bool() {
                        true => Variance::Covariant,
                        false => Variance::Contravariant,
                    };
                    if !callable
                        .return_type
                        .matches(
                            i_s,
                            &mut Matcher::default(),
                            &func.return_type(i_s),
                            variance,
                        )
                        .bool()
                    {
                        from.add_issue(
                            i_s,
                            IssueType::OperatorSignaturesAreUnsafelyOverlapping {
                                reverse_name: short_reverse_name.into(),
                                reverse_class: func.class.unwrap().format_short(i_s.db),
                                forward_class: forward.format_short(i_s.db),
                            },
                        )
                    }
                };
                match lookup_details.lookup.into_inferred().as_type(i_s) {
                    Type::Callable(c) => check(&c),
                    Type::FunctionOverload(overload) => {
                        for c in overload.iter_functions() {
                            check(c)
                        }
                    }
                    Type::Any(_) | Type::CustomBehavior(_) => (),
                    _ => from.add_issue(
                        i_s,
                        IssueType::ForwardOperatorIsNotCallable {
                            forward_name: normal_magic,
                        },
                    ),
                }
            },
        )
    }

    fn check_inplace_methods(&self, func: Function, inplace_magic_name: &str) {
        let i_s = self.i_s;
        let Some(normal_magic_name) = INPLACE_TO_NORMAL_METHODS.get(inplace_magic_name) else {
            return
        };
        let normal_method = func
            .class
            .unwrap()
            .lookup_without_descriptors(i_s, func.node_ref, normal_magic_name)
            .lookup;
        let inplace_method = func
            .class
            .unwrap()
            .lookup_without_descriptors(i_s, func.node_ref, func.name())
            .lookup;
        if !normal_method
            .into_inferred()
            .as_cow_type(i_s)
            .is_simple_super_type_of(i_s, &inplace_method.into_inferred().as_cow_type(i_s))
            .bool()
        {
            func.add_issue_for_declaration(
                self.i_s,
                IssueType::SignaturesAreIncompatible {
                    name1: func.name().into(),
                    name2: normal_magic_name,
                },
            )
        }
    }

    fn check_magic_exit(&mut self, function: Function) {
        // Check if __exit__ has the return type bool and raise an error if all returns return
        // False.
        if !function
            .return_type(self.i_s)
            .iter_with_unpacked_unions()
            .any(|t| t == &self.i_s.db.python_state.bool_type())
        {
            return;
        }
        let mut had_return = false;
        for return_or_yield in function.iter_return_or_yield() {
            let ReturnOrYield::Return(return_) = return_or_yield else {
                continue
            };
            had_return = true;
            if let Some(star_expressions) = return_.star_expressions() {
                let inf =
                    self.infer_star_expressions(star_expressions, &mut ResultContext::Unknown);
                if !matches!(
                    inf.as_cow_type(self.i_s).as_ref(),
                    Type::Literal(Literal {
                        kind: LiteralKind::Bool(false),
                        ..
                    })
                ) {
                    return;
                }
            }
        }
        if had_return {
            function.add_issue_for_declaration(self.i_s, IssueType::IncorrectExitReturn);
        }
    }
}

fn valid_raise_type(i_s: &InferenceState, from: NodeRef, t: &Type, allow_none: bool) -> bool {
    let db = i_s.db;
    let check = |cls: Class| {
        cls.incomplete_mro(db)
            || cls.class_link_in_mro(db, db.python_state.base_exception_node_ref().as_link())
    };
    match t {
        Type::Class(c) => check(c.class(db)),
        Type::Type(t) => match t.as_ref() {
            Type::Class(c) => {
                let cls = c.class(db);
                cls.execute(
                    i_s,
                    &NoArgs::new(from),
                    &mut ResultContext::Unknown,
                    OnTypeError::new(&|_, _, _, _| {
                        unreachable!(
                            "Type errors should not be possible, because there are no params"
                        )
                    }),
                    false,
                );
                check(cls)
            }
            _ => false,
        },
        Type::Any(_) => true,
        Type::Never => todo!(),
        Type::Union(union) => union
            .iter()
            .all(|t| valid_raise_type(i_s, from, t, allow_none)),
        Type::None if allow_none => true,
        _ => false,
    }
}

enum ExceptType {
    ContainsOnlyBaseExceptions,
    HasExceptionGroup,
    Invalid,
}

fn except_type(i_s: &InferenceState, t: &Type, allow_tuple: bool) -> ExceptType {
    match t {
        Type::Type(t) => {
            let db = i_s.db;
            if let Some(cls) = t.maybe_class(i_s.db) {
                if cls.is_base_exception_group(i_s.db) {
                    return ExceptType::HasExceptionGroup;
                } else if cls.is_base_exception(i_s.db) {
                    return ExceptType::ContainsOnlyBaseExceptions;
                }
            }
            ExceptType::Invalid
        }
        Type::Any(_) => ExceptType::ContainsOnlyBaseExceptions,
        Type::Tuple(content) if allow_tuple => match &content.args {
            TupleArgs::FixedLen(ts) => {
                let mut result = ExceptType::ContainsOnlyBaseExceptions;
                for t in ts.iter() {
                    match except_type(i_s, t, false) {
                        ExceptType::ContainsOnlyBaseExceptions => (),
                        x @ ExceptType::HasExceptionGroup => result = x,
                        ExceptType::Invalid => return ExceptType::Invalid,
                    }
                }
                result
            }
            TupleArgs::ArbitraryLen(t) => except_type(i_s, t, false),
            TupleArgs::WithUnpack(_) => todo!(),
        },
        Type::Union(union) => {
            let mut result = ExceptType::ContainsOnlyBaseExceptions;
            for t in union.iter() {
                match except_type(i_s, t, allow_tuple) {
                    ExceptType::ContainsOnlyBaseExceptions => (),
                    x @ ExceptType::HasExceptionGroup => result = x,
                    ExceptType::Invalid => return ExceptType::Invalid,
                }
            }
            result
        }
        _ => ExceptType::Invalid,
    }
}

pub fn await_aiter_and_next(i_s: &InferenceState, base: Inferred, from: NodeRef) -> Inferred {
    await_(
        i_s,
        base.type_lookup_and_execute(i_s, from, "__aiter__", &NoArgs::new(from), &|t| {
            from.add_issue(
                i_s,
                IssueType::AsyncNotIterable {
                    type_: t.format_short(i_s.db),
                },
            )
        })
        .type_lookup_and_execute_with_attribute_error(
            i_s,
            from,
            "__anext__",
            &NoArgs::new(from),
        ),
        from,
        r#""async for""#,
        false,
    )
}

fn try_pretty_format(
    notes: &mut Vec<Box<str>>,
    i_s: &InferenceState,
    t: &Type,
    class_lookup_result: LookupResult,
) {
    let prefix = "         ";
    if let Some(inf) = class_lookup_result.into_maybe_inferred() {
        let add_kind_info = |notes: &mut Vec<Box<str>>, kind| match kind {
            FunctionKind::Classmethod { .. } => notes.push(format!("{prefix}@classmethod").into()),
            FunctionKind::Staticmethod { .. } => {
                notes.push(format!("{prefix}@staticmethod").into())
            }
            _ => (),
        };
        match inf.as_cow_type(i_s).as_ref() {
            Type::Callable(c) if !matches!(c.kind, FunctionKind::Property { .. }) => {
                add_kind_info(notes, c.kind);
                notes.push(
                    format!(
                        "{prefix}{}",
                        c.format_pretty(&FormatData::new_short(i_s.db))
                    )
                    .into(),
                );
                return;
            }
            Type::FunctionOverload(overloads) => {
                for c in overloads.iter_functions() {
                    notes.push(format!("{prefix}@overload").into());
                    add_kind_info(notes, c.kind);
                    notes.push(
                        format!(
                            "{prefix}{}",
                            c.format_pretty(&FormatData::new_short(i_s.db))
                        )
                        .into(),
                    );
                }
                return;
            }
            _ => (),
        }
    }
    notes.push(format!("{prefix}{}", t.format_short(i_s.db)).into())
}

fn is_overload_unmatchable(
    i_s: &InferenceState,
    c1: &CallableContent,
    c2: &CallableContent,
) -> bool {
    let mut matcher = Matcher::new_reverse_callable_matcher(c1);
    let result = matches_params(i_s, &mut matcher, &c2.params, &c1.params);
    matches!(result, Match::True { with_any: false })
}

fn find_and_check_override(
    i_s: &InferenceState,
    from: NodeRef,
    override_class: Class,
    name: &str,
    has_override_decorator: bool,
) {
    let instance = Instance::new(override_class, None);
    let original_details = instance.lookup_and_maybe_ignore_super_count(
        i_s,
        |issue| from.add_issue(i_s, issue),
        name,
        LookupKind::Normal,
        1,
    );
    if original_details.lookup.is_some() {
        let override_details = instance.lookup_with_details(
            i_s,
            |issue| from.add_issue(i_s, issue),
            name,
            LookupKind::Normal,
        );
        check_override(
            i_s,
            from,
            original_details,
            override_details,
            name,
            |db, c| c.name(db),
            None,
        )
    } else if has_override_decorator {
        from.add_issue(i_s, IssueType::MissingBaseForOverride { name: name.into() });
    }
}

fn check_override(
    i_s: &InferenceState,
    from: NodeRef,
    original_lookup_details: LookupDetails,
    override_lookup_details: LookupDetails,
    name: &str,
    original_class_name: impl for<'x> Fn(&'x Database, &'x TypeOrClass) -> &'x str,
    original_formatter: Option<&dyn Fn() -> String>,
) {
    let original_inf = original_lookup_details.lookup.into_inferred();
    let original_t = original_inf.as_cow_type(i_s);
    let original_class = original_lookup_details.class;
    let override_inf = override_lookup_details.lookup.into_inferred();
    let override_t = override_inf.as_cow_type(i_s);
    let override_t = override_t.as_ref();
    let TypeOrClass::Class(override_class) = override_lookup_details.class else {
        unreachable!();
    };

    let kind = LookupKind::Normal;
    let maybe_func = || match override_t {
        Type::Callable(c) if c.defined_at.file == from.file_index() => {
            let node_ref = NodeRef::from_link(i_s.db, c.defined_at);
            node_ref
                .maybe_function()
                .map(|func| Function::new(node_ref, None))
                .filter(|func| func.node().name_definition().index() == from.node_index)
        }
        _ => None,
    };

    let mut match_ = original_t.is_super_type_of(
        i_s,
        &mut Matcher::default().with_ignore_positional_param_names(),
        &override_t,
    );

    let mut op_method_wider_note = false;
    if let Type::FunctionOverload(override_overload) = override_t {
        if match_.bool()
            && FORWARD_OP_METHODS.contains(name)
            && operator_domain_is_widened(i_s, override_overload, &original_t)
        {
            // Reverse operators lead to weird behavior when overloads widen. If you want to
            // understand why this is an issue, please look at testUnsafeDunderOverlapInSubclass.
            op_method_wider_note = true;
            match_ = Match::new_false();
        }
    }
    use AttributeKind::*;
    match (
        original_lookup_details.attr_kind,
        override_lookup_details.attr_kind,
    ) {
        (
            AttributeKind::Property {
                writable: writable1,
            },
            AttributeKind::Property {
                writable: writable2,
            },
        ) => {
            if writable1 && !writable2 {
                let func = from
                    .add_to_node_index(NAME_DEF_TO_NAME_DIFFERENCE as i64)
                    .maybe_name_of_function()
                    .unwrap();
                Function::new(NodeRef::new(from.file, func.index()), None)
                    .add_issue_onto_start_including_decorator(
                        i_s,
                        IssueType::ReadOnlyPropertyCannotOverwriteReadWriteProperty,
                    );
            }
        }
        (Classmethod | Staticmethod, DefMethod) => {
            // Some method types may be overridden, because they still work the same way on class
            // and instance, others not.
            match_ = Match::new_false();
        }
        (ClassVar, AnnotatedAttribute) => from.add_issue(
            i_s,
            IssueType::CannotOverrideClassVariableWithInstanceVariable {
                base_class: original_class_name(i_s.db, &original_class).into(),
            },
        ),
        (AnnotatedAttribute, ClassVar) => from.add_issue(
            i_s,
            IssueType::CannotOverrideInstanceVariableWithClassVariable {
                base_class: original_class_name(i_s.db, &original_class).into(),
            },
        ),
        _ => (),
    }
    if !match_.bool() {
        let db = i_s.db;
        let mut emitted = false;
        // Mypy helps the user a bit by formatting different error messages for similar
        // signatures. Try to make this as similar as possible to Mypy.
        match override_func_infos(&override_t, &original_t) {
            Some(OverrideFuncInfos::CallablesSameParamLen(got_c, expected_c)) => {
                let supertype = original_class_name(db, &original_class);

                // First check params
                let CallableParams::Simple(params1) = &got_c.params else {
                    unreachable!()
                };
                let CallableParams::Simple(params2) = &expected_c.params else {
                    unreachable!()
                };
                for (i, (param1, param2)) in params1.iter().zip(params2.iter()).enumerate() {
                    let Some(t1) = param1.type_.maybe_type() else {
                        continue;
                    };
                    let Some(t2) = param2.type_.maybe_type() else {
                        continue;
                    };
                    let t1 = got_c.erase_func_type_vars_for_type(db, t1);
                    if !t1.is_simple_super_type_of(i_s, &t2).bool() {
                        let issue = IssueType::ArgumentIncompatibleWithSupertype {
                            message: format!(
                                r#"Argument {} of "{name}" is incompatible with supertype "{supertype}"; supertype defines the argument type as "{}""#,
                                i + 1,
                                t2.format_short(db),
                            ).into(),
                            eq_class: (name == "__eq__").then(|| override_class.name().into()),
                            add_liskov_note: name != "__post_init__",
                        };
                        match &param1.name {
                            Some(DbString::StringSlice(s)) if maybe_func().is_some() => {
                                from.file.add_issue(
                                    i_s,
                                    Issue {
                                        type_: issue,
                                        start_position: s.start,
                                        end_position: s.end,
                                    },
                                );
                            }
                            _ => from.add_issue(i_s, issue),
                        }
                        emitted = true;
                    }
                }

                // Then the return type
                let got_ret = got_c.erase_func_type_vars_for_type(db, &got_c.return_type);
                let expected_ret =
                    expected_c.erase_func_type_vars_for_type(db, &expected_c.return_type);
                if !got_c
                    .return_type
                    .is_simple_sub_type_of(i_s, &expected_c.return_type)
                    .bool()
                {
                    let mut async_note = None;
                    if is_async_iterator_without_async(i_s, &expected_ret, &got_ret) {
                        async_note = Some(format!(r#"Consider declaring "{name}" in supertype "{supertype}" without "async""#).into())
                    }

                    let issue = IssueType::ReturnTypeIncompatibleWithSupertype {
                        message: format!(
                            r#"Return type "{}" of "{name}" incompatible with return type "{}" in supertype "{supertype}""#,
                            got_ret.format_short(db),
                            expected_ret.format_short(db),
                        ),
                        async_note,
                    };
                    if let Some(func) = maybe_func() {
                        func.add_issue_for_declaration(i_s, issue)
                    } else {
                        from.add_issue(i_s, issue);
                    }
                    emitted = true
                }
            }
            Some(OverrideFuncInfos::Mixed) => (),
            Some(OverrideFuncInfos::BothOverloads(got, expected)) => {
                let mut previous_match_right_index = 0;
                'outer: for c1 in expected.iter_functions() {
                    for (right_index, c2) in got.iter_functions().enumerate() {
                        let m = Matcher::default().matches_callable(i_s, c1, c2);
                        if m.bool() {
                            if previous_match_right_index <= right_index {
                                previous_match_right_index = right_index;
                                continue 'outer;
                            } else {
                                emitted = true;
                                from.add_issue(
                                    i_s,
                                    IssueType::OverloadOrderMustMatchSupertype {
                                        name: name.into(),
                                        base_class: original_class_name(db, &original_class).into(),
                                    },
                                );
                                break 'outer;
                            }
                        }
                    }
                    break;
                }
            }
            None => {
                emitted = true;
                from.add_issue(
                    i_s,
                    IssueType::IncompatibleAssignmentInSubclass {
                        got: override_t.format_short(i_s.db),
                        expected: original_t.format_short(i_s.db),
                        base_class: original_class_name(i_s.db, &original_class).into(),
                    },
                )
            }
        }
        if !emitted {
            let mut notes = vec![];
            notes.push("     Superclass:".into());
            if let Some(original_formatter) = original_formatter {
                notes.push(format!("         {}", original_formatter()).into());
            } else {
                try_pretty_format(
                    &mut notes,
                    &i_s.with_class_context(&match original_class {
                        TypeOrClass::Class(c) => c,
                        TypeOrClass::Type(_) => override_class,
                    }),
                    &original_t,
                    override_class
                        .lookup_and_class_and_maybe_ignore_self(i_s, |_| todo!(), name, kind, true)
                        .lookup,
                );
            }
            notes.push("     Subclass:".into());
            try_pretty_format(
                &mut notes,
                &i_s.with_class_context(&override_class),
                &override_t,
                override_class.lookup(i_s, |_| todo!(), name, kind),
            );

            if op_method_wider_note {
                notes.push(
                    "Overloaded operator methods can't have wider argument types in overrides"
                        .into(),
                )
            }

            let issue = IssueType::SignatureIncompatibleWithSupertype {
                name: name.into(),
                base_class: original_class_name(i_s.db, &original_class).into(),
                notes: notes.into(),
            };
            if let Some(func) = maybe_func() {
                func.add_issue_for_declaration(i_s, issue)
            } else {
                from.add_issue(i_s, issue)
            }
        }
    }
}

fn is_async_iterator_without_async(
    i_s: &InferenceState,
    original: &Type,
    override_: &Type,
) -> bool {
    let db = i_s.db;
    match override_ {
        Type::Class(c) if c.link == db.python_state.async_iterator_link() => match original {
            Type::Class(c) if c.link == db.python_state.coroutine_link() => {
                let check = c.class(db).nth_type_argument(db, 2);
                override_.is_simple_same_type(i_s, &check).bool()
            }
            _ => false,
        },
        _ => false,
    }
}

enum OverrideFuncInfos<'t1, 't2> {
    CallablesSameParamLen(&'t1 CallableContent, &'t2 CallableContent),
    BothOverloads(&'t1 FunctionOverload, &'t2 FunctionOverload),
    Mixed,
}

fn override_func_infos<'t1, 't2>(
    t1: &'t1 Type,
    t2: &'t2 Type,
) -> Option<OverrideFuncInfos<'t1, 't2>> {
    match (t1, t2) {
        (Type::Callable(c1), Type::Callable(c2)) => Some(match (&c1.params, &c2.params) {
            (CallableParams::Simple(p1), CallableParams::Simple(p2)) if p1.len() == p2.len() => {
                OverrideFuncInfos::CallablesSameParamLen(c1, c2)
            }
            _ => OverrideFuncInfos::Mixed,
        }),
        (Type::FunctionOverload(o1), Type::FunctionOverload(o2)) => {
            Some(OverrideFuncInfos::BothOverloads(&o1, &o2))
        }
        _ => (t1.is_func_or_overload() || t2.is_func_or_overload())
            .then_some(OverrideFuncInfos::Mixed),
    }
}

fn operator_domain_is_widened(
    i_s: &InferenceState,
    override_overload: &FunctionOverload,
    original: &Type,
) -> bool {
    override_overload.iter_functions().any(|overload_func| {
        let widens_callable = |original: &Rc<CallableContent>| {
            let Some(original_domain) = original.first_positional_type() else {
                return false
            };
            if let Some(override_domain) = overload_func.first_positional_type() {
                !original_domain
                    .is_simple_super_type_of(i_s, &override_domain)
                    .bool()
            } else {
                false
            }
        };
        match original {
            Type::Callable(c) => widens_callable(c),
            Type::FunctionOverload(o) => o.iter_functions().all(widens_callable),
            _ => unreachable!(),
        }
    })
}

fn check_protocol_type_var_variances(i_s: &InferenceState, class: Class) {
    for (i, tv_like) in class.type_vars(i_s).iter().enumerate() {
        let TypeVarLike::TypeVar(tv) = tv_like else {
            continue
        };
        let replace_protocol = |is_upper: bool| {
            Type::new_class(
                class.node_ref.as_link(),
                ClassGenerics::List(GenericsList::new_generics(
                    class
                        .type_vars(i_s)
                        .iter()
                        .enumerate()
                        .map(|(j, tv_like)| {
                            if i == j {
                                GenericItem::TypeArg(if is_upper {
                                    i_s.db.python_state.object_type()
                                } else {
                                    Type::Never
                                })
                            } else {
                                tv_like.as_any_generic_item()
                            }
                        })
                        .collect(),
                )),
            )
        };
        let p_upper_bound = replace_protocol(true);
        let p_lower_bound = replace_protocol(false);

        let match_protocol = |t1: &Type, t2| {
            t1.maybe_class(i_s.db)
                .unwrap()
                .check_protocol_match(i_s, &mut Matcher::default(), t2)
                .bool()
        };
        let mut expected_variance = Variance::Invariant;
        if match_protocol(&p_upper_bound, &p_lower_bound) {
            expected_variance = Variance::Covariant
        } else if match_protocol(&p_lower_bound, &p_upper_bound) {
            expected_variance = Variance::Contravariant
        }
        if tv.variance != expected_variance {
            NodeRef::new(class.node_ref.file, class.node().name().index()).add_issue(
                i_s,
                IssueType::ProtocolWrongVariance {
                    type_var_name: tv.name(i_s.db).into(),
                    actual_variance: tv.variance,
                    expected_variance,
                },
            )
        }
    }
}
