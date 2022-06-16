mod strings;

use std::iter::{Skip, StepBy};
use std::str::from_utf8;

use parsa_python::{
    parse,
    NonterminalType::*,
    PyNode, PyNodeType,
    PyNodeType::{ErrorNonterminal, ErrorTerminal, Nonterminal, Terminal},
    PyTree, SearchIterator, SiblingIterator, TerminalType,
};
pub use parsa_python::{CodeIndex, NodeIndex};
use strings::starts_with_string;
pub use strings::PythonString;

pub struct Tree(PyTree);

impl Tree {
    pub fn parse(code: String) -> Self {
        Self(parse(code))
    }

    pub fn length(&self) -> usize {
        self.0.length()
    }

    pub fn code(&self) -> &str {
        self.0.as_code()
    }

    pub fn root(&self) -> File {
        File::new(self.0.root_node())
    }

    pub fn maybe_expression(&self) -> Option<Expression> {
        let mut node = self.0.root_node();
        for (nonterminal, expected_node_count) in [
            (stmt, 2),
            (simple_stmts, 1),
            (simple_stmt, 2),
            (star_expressions, 1),
            (expression, 1),
        ] {
            if node.iter_children().count() != expected_node_count {
                return None;
            }
            node = node.nth_child(0);
            if !node.is_type(Nonterminal(nonterminal)) {
                return None;
            }
        }
        Some(Expression::new(node))
    }

    pub fn node_start_position(&self, index: NodeIndex) -> CodeIndex {
        self.0.node_by_index(index).start()
    }

    pub fn node_end_position(&self, index: NodeIndex) -> CodeIndex {
        self.0.node_by_index(index).end()
    }

    pub fn node_has_type_ignore_comment(&self, index: NodeIndex) -> bool {
        self.0
            .node_by_index(index)
            .parent_until(&[Nonterminal(simple_stmt)])
            .map(|s| s.suffix().trim_start_matches(&[' ', '\t'][..]) == "# type: ignore")
            .unwrap_or(false)
    }

    pub fn debug_info(&self, index: NodeIndex) -> String {
        format!("{:?}", self.0.node_by_index(index))
    }

    pub fn code_of_index(&self, index: NodeIndex) -> &str {
        self.0.node_by_index(index).as_code()
    }

    pub fn short_debug_of_index(&self, index: NodeIndex) -> &str {
        let node = self.0.node_by_index(index);
        node.as_code().get(..40).unwrap_or_else(|| node.as_code())
    }
}

pub trait InterestingNodeSearcher<'db> {
    fn search_interesting_nodes(&self) -> InterestingNodes<'db>;
}

// A bit special, since this does not make much sense except for zuban's NameBinder.
pub enum InterestingNode<'db> {
    Name(Name<'db>),
    Lambda(Lambda<'db>),
    Comprehension(Comprehension<'db>),
    DictComprehension(DictComprehension<'db>),
    YieldExpr(YieldExpr<'db>),
    ReturnStmt(ReturnStmt<'db>),
}
pub struct InterestingNodes<'db>(SearchIterator<'db>);

impl<'db> Iterator for InterestingNodes<'db> {
    type Item = InterestingNode<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| {
            if n.is_type(Terminal(TerminalType::Name)) {
                InterestingNode::Name(Name::new(n))
            } else if n.is_type(Nonterminal(return_stmt)) {
                InterestingNode::ReturnStmt(ReturnStmt::new(n))
            } else if n.is_type(Nonterminal(yield_expr)) {
                InterestingNode::YieldExpr(YieldExpr::new(n))
            } else if n.is_type(Nonterminal(lambda)) {
                InterestingNode::Lambda(Lambda::new(n))
            } else if n.is_type(Nonterminal(comprehension)) {
                InterestingNode::Comprehension(Comprehension::new(n))
            } else {
                debug_assert_eq!(n.type_(), Nonterminal(dict_comprehension));
                InterestingNode::DictComprehension(DictComprehension::new(n))
            }
        })
    }
}

macro_rules! create_struct {
    ($name:ident: $type:expr) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $name<'db> {
            node: PyNode<'db>,
        }

        impl<'db> $name<'db> {
            #[inline]
            pub fn new(node: PyNode<'db>) -> Self {
                debug_assert_eq!(node.type_(), $type, "{:?} {:?}", node, node.parent());
                Self { node }
            }

            #[inline]
            pub fn by_index(tree: &'db Tree, index: NodeIndex) -> Self {
                Self::new(tree.0.node_by_index(index))
            }

            #[inline]
            pub fn maybe_by_index(tree: &'db Tree, node_index: NodeIndex) -> Option<Self> {
                let node = tree.0.node_by_index(node_index);
                node.is_type($type).then(|| Self::new(node))
            }

            #[inline]
            pub fn index(&self) -> NodeIndex {
                self.node.index
            }

            #[inline]
            pub fn start(&self) -> CodeIndex {
                self.node.start()
            }

            #[inline]
            pub fn end(&self) -> CodeIndex {
                self.node.end()
            }

            pub fn short_debug(&self) -> &'db str {
                self.node
                    .as_code()
                    .get(..40)
                    .unwrap_or_else(|| self.node.as_code())
            }

            pub fn suffix(&self) -> &'db str {
                self.node.suffix()
            }

            pub fn as_code(&self) -> &'db str {
                self.node.as_code()
            }
        }

        impl<'db> InterestingNodeSearcher<'db> for $name<'db> {
            fn search_interesting_nodes(&self) -> InterestingNodes<'db> {
                const SEARCH_NAMES: &[PyNodeType] = &[
                    Terminal(TerminalType::Name),
                    Nonterminal(lambda),
                    Nonterminal(comprehension),
                    Nonterminal(yield_expr),
                    Nonterminal(return_stmt),
                    Nonterminal(dict_comprehension),
                ];
                InterestingNodes(self.node.search(SEARCH_NAMES))
            }
        }
    };
}

macro_rules! create_nonterminal_structs {
    ($($name:ident: $nonterminal:ident)+) => {
        $(create_struct!{$name: Nonterminal($nonterminal)})+
    };
}

create_nonterminal_structs!(
    File: file
    Block: block

    Stmt: stmt
    ForStmt: for_stmt
    WhileStmt: while_stmt
    WithStmt: with_stmt
    IfStmt: if_stmt
    TryStmt: try_stmt
    ElseBlock: else_block
    ExceptBlock: except_block
    FinallyBlock: finally_block
    MatchStmt: match_stmt
    AsyncStmt: async_stmt

    GlobalStmt: global_stmt
    DelStmt: del_stmt
    PassStmt: pass_stmt
    AssertStmt: assert_stmt
    BreakStmt: break_stmt
    ContinueStmt: continue_stmt
    RaiseStmt: raise_stmt
    NonlocalStmt: nonlocal_stmt

    StarExpressions: star_expressions
    StarExpressionsTuple: star_expressions
    StarExpression: star_expression
    StarNamedExpression: star_named_expression
    Expression: expression
    Ternary: expression
    NamedExpression: named_expression

    SimpleStmts: simple_stmts
    SimpleStmt: simple_stmt
    Assignment: assignment
    SingleTarget: single_target
    AugAssign: augassign

    ImportFrom: import_from
    ImportName: import_name
    DottedName: dotted_name
    DottedAsName: dotted_as_name
    ImportFromAsName: import_from_as_name

    Disjunction: disjunction
    Conjunction: conjunction
    Inversion: inversion
    Comparison: comparison
    Operand: comp_op
    BitwiseOr: bitwise_or
    BitwiseXor: bitwise_xor
    BitwiseAnd: bitwise_and
    ShiftExpr: shift_expr
    Sum: sum
    Term: term
    Factor: factor
    Power: power
    AwaitPrimary: await_primary
    Primary: primary

    PrimaryTarget: t_primary
    StarTarget: star_target

    Arguments: arguments

    NameDefinition: name_definition
    Atom: atom
    StringsOrBytes: strings
    FString: fstring
    FStringExpr: fstring_expr
    FStringFormatSpec: fstring_format_spec

    List: atom
    Set: atom
    Tuple: atom
    Dict: atom
    DictKeyValue: dict_key_value
    DictStarred: dict_starred
    Comprehension: comprehension
    DictComprehension: dict_comprehension
    ForIfClauses: for_if_clauses
    SyncForIfClause: sync_for_if_clause
    CompIf: comp_if
    Slices: slices
    Slice: slice

    Decorated: decorated
    Decorators: decorators
    Decorator: decorator
    ClassDef: class_def

    FunctionDef: function_def
    FunctionDefParameters: function_def_parameters
    ReturnAnnotation: return_annotation
    Annotation: annotation
    ReturnStmt: return_stmt
    YieldExpr: yield_expr
    YieldFrom: yield_from
    Lambda: lambda

    StarTargets: star_targets
    WithItems: with_items
    WithItem: with_item
);

create_struct!(Name: Terminal(TerminalType::Name));
create_struct!(Int: Terminal(TerminalType::Number));
create_struct!(Float: Terminal(TerminalType::Number));
create_struct!(Complex: Terminal(TerminalType::Number));
create_struct!(PyString: Terminal(TerminalType::String));
create_struct!(Bytes: Terminal(TerminalType::Bytes));
create_struct!(FStringString: Terminal(TerminalType::FStringString));
create_struct!(Keyword: PyNodeType::Keyword);

impl<'db> Name<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.node.as_code()
    }

    pub fn is_reference(&self) -> bool {
        !self
            .node
            .parent()
            .unwrap()
            .is_type(Nonterminal(name_definition))
    }

    pub fn name_definition(&self) -> Option<NameDefinition<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(name_definition)) {
            Some(NameDefinition::new(parent))
        } else {
            None
        }
    }

    pub fn name_def_index(&self) -> NodeIndex {
        debug_assert_eq!(self.name_definition().unwrap().index(), self.index() - 1);
        self.index() - 1
    }

    pub fn expect_function_def(&self) -> FunctionDef<'db> {
        FunctionDef::new(self.node.parent().unwrap().parent().unwrap())
    }

    pub fn expect_class_def(&self) -> ClassDef<'db> {
        ClassDef::new(self.node.parent().unwrap().parent().unwrap())
    }

    pub fn expect_type(&self) -> TypeLike<'db> {
        let node = self
            .node
            .parent_until(&[
                Nonterminal(class_def),
                Nonterminal(assignment),
                Nonterminal(function_def),
                Nonterminal(import_from_as_name),
                Nonterminal(dotted_as_name),
                Nonterminal(stmt),
            ])
            .expect("There should always be a stmt");
        if node.is_type(Nonterminal(class_def)) {
            TypeLike::ClassDef(ClassDef::new(node))
        } else if node.is_type(Nonterminal(assignment)) {
            TypeLike::Assignment(Assignment::new(node))
        } else if node.is_type(Nonterminal(function_def)) {
            TypeLike::Function(FunctionDef::new(node))
        } else if node.is_type(Nonterminal(stmt)) {
            TypeLike::Other
        } else {
            TypeLike::Import
        }
    }

    pub fn has_self_param_position(&self) -> bool {
        // Parents are name_definition/param_no_default/parameters
        let param = self.node.parent().unwrap().parent().unwrap();
        let params = param.parent().unwrap();
        // Could also be a kwarg, which is never a self
        params.is_type(Nonterminal(parameters)) && params.index + 1 == param.index
    }

    pub fn parent(&self) -> NameParent<'db> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(atom)) {
            NameParent::Atom
        } else if parent.is_type(Nonterminal(name_definition)) {
            NameParent::NameDefinition(NameDefinition::new(parent))
        } else if parent.is_type(Nonterminal(primary)) {
            NameParent::Primary(Primary::new(parent))
        } else if parent.is_type(Nonterminal(global_stmt)) {
            NameParent::GlobalStmt
        } else if parent.is_type(Nonterminal(nonlocal_stmt)) {
            NameParent::NonlocalStmt
        } else {
            NameParent::Other
        }
    }

    pub fn simple_param_type(&self) -> SimpleParamType {
        let param = self.node.parent().unwrap().parent().unwrap();
        if param.is_type(Nonterminal(starred_param))
            || param.is_type(Nonterminal(lambda_starred_param))
        {
            SimpleParamType::MultiArgs
        } else if param.is_type(Nonterminal(double_starred_param))
            || param.is_type(Nonterminal(lambda_double_starred_param))
        {
            SimpleParamType::MultiKwargs
        } else {
            SimpleParamType::Normal
        }
    }
}

#[derive(Debug)]
pub enum NameParent<'db> {
    NameDefinition(NameDefinition<'db>),
    Primary(Primary<'db>),
    Atom,
    GlobalStmt,
    NonlocalStmt,
    Other,
}

pub enum FunctionOrLambda<'db> {
    Function(FunctionDef<'db>),
    Lambda(Lambda<'db>),
}

impl<'db> Int<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.node.as_code()
    }
}

#[derive(Debug)]
pub enum StmtLike<'db> {
    Stmt(Stmt<'db>),
    Lambda(Lambda<'db>),
    Comprehension(Comprehension<'db>),
    DictComprehension(DictComprehension<'db>),
}

impl<'db> StmtLike<'db> {
    #[inline]
    pub fn index(&self) -> NodeIndex {
        match self {
            StmtLike::Stmt(n) => n.index(),
            StmtLike::Lambda(n) => n.index(),
            StmtLike::Comprehension(n) => n.index(),
            StmtLike::DictComprehension(n) => n.index(),
        }
    }
}

#[derive(Debug)]
pub enum TypeLike<'db> {
    Assignment(Assignment<'db>),
    ClassDef(ClassDef<'db>),
    Function(FunctionDef<'db>),
    Import,
    Other,
}

impl<'db> Keyword<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.node.as_code()
    }

    pub fn maybe_primary_parent(&self) -> Option<Primary<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(primary)) {
            Some(Primary::new(parent))
        } else {
            None
        }
    }
}

impl<'db> File<'db> {
    pub fn iter_stmts(&self) -> StmtIterator<'db> {
        StmtIterator(self.node.iter_children())
    }
}

impl<'db> List<'db> {
    pub fn unpack(&self) -> Option<ListOrSetElementIterator<'db>> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(star_named_expressions)) {
            Some(ListOrSetElementIterator(n.iter_children().step_by(2)))
        } else {
            assert_eq!(n.type_(), PyNodeType::Keyword);
            None
        }
    }
}

#[derive(Debug)]
pub struct ListOrSetElementIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for ListOrSetElementIterator<'db> {
    type Item = StarLikeExpression<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|next| {
            if next.is_type(Nonterminal(named_expression)) {
                StarLikeExpression::NamedExpression(NamedExpression::new(next))
            } else {
                StarLikeExpression::StarNamedExpression(StarNamedExpression::new(next))
            }
        })
    }
}

impl<'db> Set<'db> {
    pub fn unpack(&self) -> Option<ListOrSetElementIterator<'db>> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(star_named_expressions)) {
            Some(ListOrSetElementIterator(n.iter_children().step_by(2)))
        } else {
            assert_eq!(n.type_(), PyNodeType::Keyword);
            None
        }
    }
}

pub enum StarLikeExpression<'db> {
    Expression(Expression<'db>),
    NamedExpression(NamedExpression<'db>),
    StarExpression(StarExpression<'db>),
    StarNamedExpression(StarNamedExpression<'db>),
}

impl<'db> Tuple<'db> {
    pub fn iter(&self) -> TupleLikeIterator<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(tuple_content)) {
            TupleLikeIterator::Elements(n.iter_children().step_by(2))
        } else {
            debug_assert_eq!(n.as_code(), ")");
            TupleLikeIterator::Empty
        }
    }
}

pub enum TupleLikeIterator<'db> {
    Elements(StepBy<SiblingIterator<'db>>),
    Empty,
}

impl<'db> Iterator for TupleLikeIterator<'db> {
    type Item = StarLikeExpression<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Elements(iterator) => iterator.next().map(|node| {
                if node.is_type(Nonterminal(named_expression)) {
                    StarLikeExpression::NamedExpression(NamedExpression::new(node))
                } else if node.is_type(Nonterminal(star_named_expression)) {
                    StarLikeExpression::StarNamedExpression(StarNamedExpression::new(node))
                } else {
                    debug_assert_eq!(node.type_(), Nonterminal(star_named_expressions));
                    *self = Self::Elements(node.iter_children().step_by(2));
                    self.next().unwrap()
                }
            }),
            Self::Empty => None,
        }
    }
}

impl<'db> StarExpressionsTuple<'db> {
    pub fn iter(&self) -> StarExpressionsIterator<'db> {
        StarExpressionsIterator(self.node.iter_children().step_by(2))
    }
}

pub struct StarExpressionsIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for StarExpressionsIterator<'db> {
    type Item = StarLikeExpression<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|node| {
            if node.is_type(Nonterminal(expression)) {
                StarLikeExpression::Expression(Expression::new(node))
            } else {
                debug_assert_eq!(node.type_(), Nonterminal(star_expression));
                StarLikeExpression::StarExpression(StarExpression::new(node))
            }
        })
    }
}

impl<'db> Dict<'db> {
    pub fn iter_elements(&self) -> DictElementIterator<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(dict_content)) {
            DictElementIterator::Elements(n.iter_children().step_by(2))
        } else {
            DictElementIterator::Empty
        }
    }
}

pub enum DictElementIterator<'db> {
    Elements(StepBy<SiblingIterator<'db>>),
    Empty,
}

impl<'db> Iterator for DictElementIterator<'db> {
    type Item = DictElement<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            DictElementIterator::Elements(iterator) => iterator.next().map(|node| {
                if node.is_type(Nonterminal(dict_key_value)) {
                    DictElement::KeyValue(DictKeyValue::new(node))
                } else {
                    DictElement::DictStarred(DictStarred::new(node))
                }
            }),
            DictElementIterator::Empty => None,
        }
    }
}

pub enum DictElement<'db> {
    KeyValue(DictKeyValue<'db>),
    DictStarred(DictStarred<'db>),
}

impl<'db> DictKeyValue<'db> {
    pub fn key(self) -> Expression<'db> {
        Expression::new(self.node.nth_child(0))
    }

    pub fn value(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(2))
    }
}

impl<'db> Expression<'db> {
    pub fn unpack(self) -> ExpressionContent<'db> {
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();
        if first.is_type(Nonterminal(lambda)) {
            ExpressionContent::Lambda(Lambda::new(first))
        } else if iter.next().is_none() {
            ExpressionContent::ExpressionPart(ExpressionPart::new(first))
        } else {
            ExpressionContent::Ternary(Ternary::new(self.node))
        }
    }

    pub fn search_names(&self) -> NameIterator<'db> {
        NameIterator(self.node.search(&[Terminal(TerminalType::Name)]))
    }

    fn maybe_name_or_last_primary_name(&self) -> Option<Name<'db>> {
        match self.unpack() {
            ExpressionContent::ExpressionPart(ExpressionPart::Atom(a)) => {
                if let AtomContent::Name(n) = a.unpack() {
                    Some(n)
                } else {
                    None
                }
            }
            ExpressionContent::ExpressionPart(ExpressionPart::Primary(p)) => p.is_only_attributes(),
            _ => None,
        }
    }
}

pub enum ExpressionContent<'db> {
    ExpressionPart(ExpressionPart<'db>),
    Ternary(Ternary<'db>),
    Lambda(Lambda<'db>),
}

#[derive(Debug)]
pub enum ExpressionPart<'db> {
    Atom(Atom<'db>),
    Primary(Primary<'db>),
    AwaitPrimary(AwaitPrimary<'db>),
    Power(Power<'db>),
    Factor(Factor<'db>),
    Term(Term<'db>),
    Sum(Sum<'db>),
    ShiftExpr(ShiftExpr<'db>),
    BitwiseAnd(BitwiseAnd<'db>),
    BitwiseXor(BitwiseXor<'db>),
    BitwiseOr(BitwiseOr<'db>),
    Comparison(Comparison<'db>),
    Inversion(Inversion<'db>),
    Conjunction(Conjunction<'db>),
    Disjunction(Disjunction<'db>),
}

impl<'db> ExpressionPart<'db> {
    fn new(node: PyNode<'db>) -> Self {
        // Sorted by how often they probably appear
        if node.is_type(Nonterminal(atom)) {
            Self::Atom(Atom::new(node))
        } else if node.is_type(Nonterminal(primary)) {
            Self::Primary(Primary::new(node))
        } else if node.is_type(Nonterminal(sum)) {
            Self::Sum(Sum::new(node))
        } else if node.is_type(Nonterminal(term)) {
            Self::Term(Term::new(node))
        } else if node.is_type(Nonterminal(await_primary)) {
            Self::AwaitPrimary(AwaitPrimary::new(node))
        } else if node.is_type(Nonterminal(power)) {
            Self::Power(Power::new(node))
        } else if node.is_type(Nonterminal(factor)) {
            Self::Factor(Factor::new(node))
        } else if node.is_type(Nonterminal(shift_expr)) {
            Self::ShiftExpr(ShiftExpr::new(node))
        } else if node.is_type(Nonterminal(bitwise_and)) {
            Self::BitwiseAnd(BitwiseAnd::new(node))
        } else if node.is_type(Nonterminal(bitwise_xor)) {
            Self::BitwiseXor(BitwiseXor::new(node))
        } else if node.is_type(Nonterminal(bitwise_or)) {
            Self::BitwiseOr(BitwiseOr::new(node))
        } else if node.is_type(Nonterminal(comparison)) {
            Self::Comparison(Comparison::new(node))
        } else if node.is_type(Nonterminal(inversion)) {
            Self::Inversion(Inversion::new(node))
        } else if node.is_type(Nonterminal(conjunction)) {
            Self::Conjunction(Conjunction::new(node))
        } else if node.is_type(Nonterminal(disjunction)) {
            Self::Disjunction(Disjunction::new(node))
        } else {
            unreachable!()
        }
    }
}

impl<'db> InterestingNodeSearcher<'db> for ExpressionPart<'db> {
    fn search_interesting_nodes(&self) -> InterestingNodes<'db> {
        match self {
            Self::Atom(n) => n.search_interesting_nodes(),
            Self::Primary(n) => n.search_interesting_nodes(),
            Self::AwaitPrimary(n) => n.search_interesting_nodes(),
            Self::Power(n) => n.search_interesting_nodes(),
            Self::Factor(n) => n.search_interesting_nodes(),
            Self::Term(n) => n.search_interesting_nodes(),
            Self::Sum(n) => n.search_interesting_nodes(),
            Self::ShiftExpr(n) => n.search_interesting_nodes(),
            Self::BitwiseAnd(n) => n.search_interesting_nodes(),
            Self::BitwiseXor(n) => n.search_interesting_nodes(),
            Self::BitwiseOr(n) => n.search_interesting_nodes(),
            Self::Comparison(n) => n.search_interesting_nodes(),
            Self::Inversion(n) => n.search_interesting_nodes(),
            Self::Conjunction(n) => n.search_interesting_nodes(),
            Self::Disjunction(n) => n.search_interesting_nodes(),
        }
    }
}

impl<'db> Ternary<'db> {
    pub fn unpack(&self) -> (ExpressionPart<'db>, ExpressionPart<'db>, Expression<'db>) {
        let mut iterator = self.node.iter_children();
        let first = ExpressionPart::new(iterator.next().unwrap());
        iterator.next();
        let second = ExpressionPart::new(iterator.next().unwrap());
        iterator.next();
        let third = Expression::new(iterator.next().unwrap());
        (first, second, third)
    }
}

impl<'db> NamedExpression<'db> {
    pub fn expression(&self) -> Expression<'db> {
        match self.unpack() {
            NamedExpressionContent::Expression(expr) => expr,
            NamedExpressionContent::Definition(_, expr) => expr,
        }
    }

    pub fn unpack(self) -> NamedExpressionContent<'db> {
        let node = self.node.nth_child(0);
        if node.is_type(Nonterminal(expression)) {
            NamedExpressionContent::Expression(Expression::new(node))
        } else {
            let expr = node.nth_child(2);
            NamedExpressionContent::Definition(NameDefinition::new(node), Expression::new(expr))
        }
    }

    pub fn is_ellipsis_literal(&self) -> bool {
        if let NamedExpressionContent::Expression(e) = self.unpack() {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(a)) = e.unpack() {
                if let AtomContent::Ellipsis = a.unpack() {
                    return true;
                }
            }
        }
        false
    }

    pub fn maybe_single_string_literal(&self) -> Option<PyString<'db>> {
        if let NamedExpressionContent::Expression(e) = self.unpack() {
            if let ExpressionContent::ExpressionPart(ExpressionPart::Atom(a)) = e.unpack() {
                if let AtomContent::StringsOrBytes(s) = a.unpack() {
                    return s.maybe_single_string_literal();
                }
            }
        }
        None
    }
}

pub enum NamedExpressionContent<'db> {
    Expression(Expression<'db>),
    Definition(NameDefinition<'db>, Expression<'db>),
}

impl<'db> ForStmt<'db> {
    pub fn unpack(
        &self,
    ) -> (
        StarTargets<'db>,
        StarExpressions<'db>,
        Block<'db>,
        Option<ElseBlock<'db>>,
    ) {
        // "for" star_targets "in" star_expressions ":" block else_block?
        let mut iterator = self.node.iter_children().skip(1);
        let star_targets_ = StarTargets::new(iterator.next().unwrap());
        iterator.next();
        let exprs = StarExpressions::new(iterator.next().unwrap());
        iterator.next();
        let block_ = Block::new(iterator.next().unwrap());
        let else_block_ = iterator.next().map(ElseBlock::new);
        (star_targets_, exprs, block_, else_block_)
    }
}

impl<'db> StarTargets<'db> {
    pub fn as_target(&self) -> Target<'db> {
        Target::new(self.node)
    }
}

impl<'db> StarTarget<'db> {
    pub fn as_target(&self) -> Target<'db> {
        Target::new_non_iterator(self.node.nth_child(1))
    }
}

#[derive(Debug, Clone)]
pub struct TargetIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for TargetIterator<'db> {
    type Item = Target<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Target::new_non_iterator)
    }
}

impl<'db> TargetIterator<'db> {
    pub fn remaining_stars_and_normal_count(self) -> (usize, usize) {
        let mut star_count = 0;
        let mut after_star_count = 0;
        for t in self {
            if matches!(t, Target::Starred(_)) {
                star_count += 1;
            } else {
                after_star_count += 1;
            }
        }
        (star_count, after_star_count)
    }
}

impl<'db> Block<'db> {
    pub fn unpack(&self) -> BlockContent<'db> {
        // simple_stmts | Newline Indent stmt+ Dedent
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap();
        if first.is_type(Nonterminal(simple_stmts)) {
            BlockContent::OneLine(SimpleStmts::new(first))
        } else {
            iterator.next(); // get rid of indent leaf
            BlockContent::Indented(StmtIterator(iterator))
        }
    }
}

pub enum BlockContent<'db> {
    OneLine(SimpleStmts<'db>),
    Indented(StmtIterator<'db>),
}

pub struct StmtIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for StmtIterator<'db> {
    type Item = Stmt<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(n) = self.0.next() {
            if n.is_type(Nonterminal(stmt)) {
                Some(Self::Item::new(n))
            } else {
                debug_assert!(
                    n.is_type(Terminal(TerminalType::Dedent))
                        || n.is_type(Terminal(TerminalType::Endmarker)),
                    "{:?}",
                    n.type_()
                );
                None
            }
        } else {
            None
        }
    }
}

impl<'db> ElseBlock<'db> {
    pub fn block(&self) -> Block<'db> {
        Block::new(self.node.nth_child(1))
    }
}

impl<'db> WhileStmt<'db> {
    pub fn unpack(&self) -> (NamedExpression<'db>, Block<'db>, Option<ElseBlock<'db>>) {
        // "while" named_expression ":" block else_block?
        let mut iterator = self.node.iter_children().skip(1);
        let named = NamedExpression::new(iterator.next().unwrap());
        iterator.next();
        let block_ = Block::new(iterator.next().unwrap());
        let else_block_ = iterator.next().map(ElseBlock::new);
        (named, block_, else_block_)
    }
}

impl<'db> WithStmt<'db> {
    pub fn unpack(&self) -> (WithItems<'db>, Block<'db>) {
        // with_stmt: "with" with_items  ":" block
        let mut iterator = self.node.iter_children().skip(1);
        let with = WithItems::new(iterator.next().unwrap());
        iterator.next();
        (with, Block::new(iterator.next().unwrap()))
    }
}

impl<'db> WithItems<'db> {
    pub fn iter(&self) -> WithItemsIterator<'db> {
        WithItemsIterator(self.node.iter_children())
    }
}

pub struct WithItemsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for WithItemsIterator<'db> {
    type Item = WithItem<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for n in &mut self.0 {
            if n.is_type(Nonterminal(with_item)) {
                return Some(Self::Item::new(n));
            }
        }
        None
    }
}

impl<'db> WithItem<'db> {
    pub fn unpack(&self) -> (Expression<'db>, Option<Target<'db>>) {
        // expression ["as" star_target]
        let mut iterator = self.node.iter_children();
        let expr = iterator.next().unwrap();
        iterator.next();
        (Expression::new(expr), iterator.next().map(Target::new))
    }
}

impl<'db> IfStmt<'db> {
    pub fn iter_blocks(&self) -> IfBlockIterator<'db> {
        let mut iterator = self.node.iter_children();
        iterator.next(); // Ignore if
        IfBlockIterator(iterator)
    }
}

pub enum IfBlockType<'db> {
    If(NamedExpression<'db>, Block<'db>),
    Else(Block<'db>),
}

pub struct IfBlockIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for IfBlockIterator<'db> {
    type Item = IfBlockType<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        // "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?
        while let Some(n) = self.0.next() {
            if n.is_type(Nonterminal(named_expression)) {
                self.0.next();
                let block_ = self.0.next().unwrap();
                return Some(Self::Item::If(NamedExpression::new(n), Block::new(block_)));
            } else if n.is_type(Nonterminal(else_block)) {
                return Some(Self::Item::Else(Block::new(n.nth_child(2))));
            }
        }
        None
    }
}

impl<'db> TryStmt<'db> {
    pub fn iter_blocks(&self) -> TryBlockIterator<'db> {
        let mut iterator = self.node.iter_children();
        iterator.next(); // Ignore try
        TryBlockIterator(iterator)
    }
}

pub enum TryBlockType<'db> {
    Try(Block<'db>),
    Except(ExceptBlock<'db>),
    Else(ElseBlock<'db>),
    Finally(FinallyBlock<'db>),
}

pub struct TryBlockIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for TryBlockIterator<'db> {
    type Item = TryBlockType<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        // "try" ":" block (except_block+ else_block? finally_block? | finally_block)
        for n in &mut self.0 {
            if n.is_type(Nonterminal(block)) {
                return Some(TryBlockType::Try(Block::new(n)));
            } else if n.is_type(Nonterminal(except_block)) {
                return Some(TryBlockType::Except(ExceptBlock::new(n)));
            } else if n.is_type(Nonterminal(else_block)) {
                return Some(TryBlockType::Else(ElseBlock::new(n)));
            } else if n.is_type(Nonterminal(finally_block)) {
                return Some(TryBlockType::Finally(FinallyBlock::new(n)));
            }
        }
        None
    }
}

impl<'db> FinallyBlock<'db> {
    pub fn block(&self) -> Block<'db> {
        Block::new(self.node.nth_child(2))
    }
}

impl<'db> ExceptBlock<'db> {
    pub fn unpack(&self) -> (Expression<'db>, Option<NameDefinition<'db>>, Block<'db>) {
        // except_clause ":" block
        let mut iterator = self.node.iter_children();
        let except_clause_ = iterator.next().unwrap();
        iterator.next();
        let block_ = iterator.next().unwrap();

        // except_clause: "except" [expression ["as" name_definition]]
        let mut clause_iterator = except_clause_.iter_children();
        clause_iterator.next();
        let expr = clause_iterator.next().unwrap();
        clause_iterator.next();
        (
            Expression::new(expr),
            clause_iterator.next().map(NameDefinition::new),
            Block::new(block_),
        )
    }
}

impl<'db> Stmt<'db> {
    #[inline]
    pub fn unpack(&self) -> StmtContent<'db> {
        let child = self.node.nth_child(0);
        if child.is_type(Nonterminal(simple_stmts)) {
            StmtContent::SimpleStmts(SimpleStmts::new(child))
        } else if child.is_type(Nonterminal(function_def)) {
            StmtContent::FunctionDef(FunctionDef::new(child))
        } else if child.is_type(Nonterminal(class_def)) {
            StmtContent::ClassDef(ClassDef::new(child))
        } else if child.is_type(Nonterminal(decorated)) {
            StmtContent::Decorated(Decorated::new(child))
        } else if child.is_type(Nonterminal(if_stmt)) {
            StmtContent::IfStmt(IfStmt::new(child))
        } else if child.is_type(Nonterminal(try_stmt)) {
            StmtContent::TryStmt(TryStmt::new(child))
        } else if child.is_type(Nonterminal(for_stmt)) {
            StmtContent::ForStmt(ForStmt::new(child))
        } else if child.is_type(Nonterminal(while_stmt)) {
            StmtContent::WhileStmt(WhileStmt::new(child))
        } else if child.is_type(Nonterminal(with_stmt)) {
            StmtContent::WithStmt(WithStmt::new(child))
        } else if child.is_type(Nonterminal(match_stmt)) {
            StmtContent::MatchStmt(MatchStmt::new(child))
        } else if child.is_type(Nonterminal(async_stmt)) {
            StmtContent::AsyncStmt(AsyncStmt::new(child))
        } else {
            debug_assert_eq!(child.type_(), Terminal(TerminalType::Newline));
            StmtContent::Newline
        }
    }
}

pub enum StmtContent<'db> {
    SimpleStmts(SimpleStmts<'db>),
    FunctionDef(FunctionDef<'db>),
    ClassDef(ClassDef<'db>),
    Decorated(Decorated<'db>),
    AsyncStmt(AsyncStmt<'db>),
    IfStmt(IfStmt<'db>),
    WhileStmt(WhileStmt<'db>),
    ForStmt(ForStmt<'db>),
    TryStmt(TryStmt<'db>),
    WithStmt(WithStmt<'db>),
    MatchStmt(MatchStmt<'db>),
    Newline,
}

impl<'db> Decorated<'db> {
    pub fn decoratee(&self) -> Decoratee<'db> {
        let decoratee = self.node.nth_child(1);
        if decoratee.is_type(Nonterminal(function_def)) {
            Decoratee::FunctionDef(FunctionDef::new(decoratee))
        } else if decoratee.is_type(Nonterminal(class_def)) {
            Decoratee::ClassDef(ClassDef::new(decoratee))
        } else {
            debug_assert_eq!(decoratee.type_(), Nonterminal(async_function_def));
            Decoratee::AsyncFunctionDef(FunctionDef::new(decoratee.nth_child(1)))
        }
    }

    pub fn decorators(&self) -> Decorators<'db> {
        Decorators::new(self.node.nth_child(0))
    }
}

pub enum Decoratee<'db> {
    ClassDef(ClassDef<'db>),
    FunctionDef(FunctionDef<'db>),
    AsyncFunctionDef(FunctionDef<'db>),
}

impl<'db> Decorators<'db> {
    pub fn iter(&self) -> DecoratorIterator<'db> {
        DecoratorIterator(self.node.iter_children())
    }
}

pub struct DecoratorIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for DecoratorIterator<'db> {
    type Item = Decorator<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Self::Item::new)
    }
}

impl<'db> Decorator<'db> {
    pub fn named_expression(&self) -> NamedExpression<'db> {
        NamedExpression::new(self.node.nth_child(1))
    }
}

impl<'db> AsyncStmt<'db> {
    pub fn unpack(&self) -> AsyncStmtContent<'db> {
        let child = self.node.nth_child(1);
        if child.is_type(Nonterminal(function_def)) {
            AsyncStmtContent::FunctionDef(FunctionDef::new(child))
        } else if child.is_type(Nonterminal(for_stmt)) {
            AsyncStmtContent::ForStmt(ForStmt::new(child))
        } else {
            debug_assert_eq!(child.type_(), Nonterminal(with_stmt));
            AsyncStmtContent::WithStmt(WithStmt::new(child))
        }
    }
}

pub enum AsyncStmtContent<'db> {
    FunctionDef(FunctionDef<'db>),
    ForStmt(ForStmt<'db>),
    WithStmt(WithStmt<'db>),
}

impl<'db> SimpleStmts<'db> {
    pub fn iter(&self) -> SimpleStmtIterator<'db> {
        SimpleStmtIterator(self.node.iter_children().step_by(2))
    }
}

pub struct SimpleStmtIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for SimpleStmtIterator<'db> {
    type Item = SimpleStmt<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Self::Item::new)
    }
}

impl<'db> SimpleStmt<'db> {
    pub fn unpack(&self) -> SimpleStmtContent<'db> {
        let simple_child = self.node.nth_child(0);
        if simple_child.is_type(Nonterminal(assignment)) {
            SimpleStmtContent::Assignment(Assignment::new(simple_child))
        } else if simple_child.is_type(Nonterminal(star_expressions)) {
            SimpleStmtContent::StarExpressions(StarExpressions::new(simple_child))
        } else if simple_child.is_type(Nonterminal(return_stmt)) {
            SimpleStmtContent::ReturnStmt(ReturnStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(yield_expr)) {
            SimpleStmtContent::YieldExpr(YieldExpr::new(simple_child))
        } else if simple_child.is_type(Nonterminal(raise_stmt)) {
            SimpleStmtContent::RaiseStmt(RaiseStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_from)) {
            SimpleStmtContent::ImportFrom(ImportFrom::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_name)) {
            SimpleStmtContent::ImportName(ImportName::new(simple_child))
        } else if simple_child.is_type(Nonterminal(pass_stmt)) {
            SimpleStmtContent::PassStmt(PassStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(global_stmt)) {
            SimpleStmtContent::GlobalStmt(GlobalStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(nonlocal_stmt)) {
            SimpleStmtContent::NonlocalStmt(NonlocalStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(assert_stmt)) {
            SimpleStmtContent::AssertStmt(AssertStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(break_stmt)) {
            SimpleStmtContent::BreakStmt(BreakStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(continue_stmt)) {
            SimpleStmtContent::ContinueStmt(ContinueStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(del_stmt)) {
            SimpleStmtContent::DelStmt(DelStmt::new(simple_child))
        } else {
            unreachable!()
        }
    }

    pub fn maybe_assignment(&self) -> Option<Assignment<'db>> {
        let child = self.node.nth_child(0);
        child
            .is_type(Nonterminal(assignment))
            .then(|| Assignment::new(child))
    }

    pub fn maybe_import_from(&self) -> Option<ImportFrom<'db>> {
        let child = self.node.nth_child(0);
        child
            .is_type(Nonterminal(import_from))
            .then(|| ImportFrom::new(child))
    }
}

pub enum SimpleStmtContent<'db> {
    Assignment(Assignment<'db>),
    StarExpressions(StarExpressions<'db>),
    ReturnStmt(ReturnStmt<'db>),
    YieldExpr(YieldExpr<'db>),
    RaiseStmt(RaiseStmt<'db>),
    ImportFrom(ImportFrom<'db>),
    ImportName(ImportName<'db>),
    PassStmt(PassStmt<'db>),
    GlobalStmt(GlobalStmt<'db>),
    NonlocalStmt(NonlocalStmt<'db>),
    AssertStmt(AssertStmt<'db>),
    BreakStmt(BreakStmt<'db>),
    ContinueStmt(ContinueStmt<'db>),
    DelStmt(DelStmt<'db>),
}

impl<'db> StarExpressions<'db> {
    pub fn unpack(&self) -> StarExpressionContent<'db> {
        let mut iter = self.node.iter_children();
        let expr = iter.next().unwrap();
        if iter.next().is_none() {
            if expr.is_type(Nonterminal(expression)) {
                StarExpressionContent::Expression(Expression::new(expr))
            } else {
                StarExpressionContent::StarExpression(StarExpression::new(expr))
            }
        } else {
            StarExpressionContent::Tuple(StarExpressionsTuple::new(self.node))
        }
    }
}

pub enum StarExpressionContent<'db> {
    Expression(Expression<'db>),
    StarExpression(StarExpression<'db>),
    Tuple(StarExpressionsTuple<'db>),
}

impl<'db> StarNamedExpression<'db> {
    pub fn expression_part(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.nth_child(1))
    }
}

impl<'db> Comprehension<'db> {
    pub fn unpack(&self) -> (CommonComprehensionExpression<'db>, ForIfClauses<'db>) {
        let mut iter = self.node.iter_children();
        let expr =
            CommonComprehensionExpression::Single(NamedExpression::new(iter.next().unwrap()));
        (expr, ForIfClauses::new(iter.next().unwrap()))
    }

    pub fn is_generator(&self) -> bool {
        return self.node.next_leaf().unwrap().as_code() == ")";
    }
}

impl<'db> DictComprehension<'db> {
    pub fn unpack(&self) -> (CommonComprehensionExpression<'db>, ForIfClauses<'db>) {
        let mut iter = self.node.iter_children();
        let expr =
            CommonComprehensionExpression::DictKeyValue(DictKeyValue::new(iter.next().unwrap()));
        (expr, ForIfClauses::new(iter.next().unwrap()))
    }
}

impl<'db> ForIfClauses<'db> {
    pub fn iter(&self) -> ForIfClauseIterator<'db> {
        ForIfClauseIterator(self.node.iter_children())
    }
}

pub enum ForIfClause<'db> {
    Async(SyncForIfClause<'db>),
    Sync(SyncForIfClause<'db>),
}

pub struct ForIfClauseIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ForIfClauseIterator<'db> {
    type Item = ForIfClause<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| {
            if n.is_type(Nonterminal(sync_for_if_clause)) {
                Self::Item::Sync(SyncForIfClause::new(n))
            } else {
                Self::Item::Async(SyncForIfClause::new(n.nth_child(1)))
            }
        })
    }
}

pub enum CommonComprehensionExpression<'db> {
    Single(NamedExpression<'db>),
    DictKeyValue(DictKeyValue<'db>),
}

impl<'db> SyncForIfClause<'db> {
    pub fn unpack(&self) -> (StarTargets<'db>, ExpressionPart<'db>, CompIfIterator<'db>) {
        // "for" star_targets "in" disjunction comp_if*
        let mut iterator = self.node.iter_children();
        iterator.next();
        let star_targets_ = StarTargets::new(iterator.next().unwrap());
        iterator.next();
        let disjunction_ = ExpressionPart::new(iterator.next().unwrap());
        (star_targets_, disjunction_, CompIfIterator(iterator))
    }
}

pub struct CompIfIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for CompIfIterator<'db> {
    type Item = CompIf<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Self::Item::new)
    }
}

impl<'db> ClassDef<'db> {
    pub fn name_definition(&self) -> NameDefinition<'db> {
        NameDefinition::new(self.node.nth_child(1))
    }

    pub fn name(&self) -> Name<'db> {
        self.name_definition().name()
    }

    pub fn arguments(&self) -> Option<Arguments<'db>> {
        let args = self.node.nth_child(3);
        args.is_type(Nonterminal(arguments))
            .then(|| Arguments::new(args))
    }

    pub fn unpack(&self) -> (Option<Arguments<'db>>, Block<'db>) {
        let mut args = None;
        for child in self.node.iter_children().skip(3) {
            if child.is_type(Nonterminal(arguments)) {
                args = Some(Arguments::new(child));
            } else if child.is_type(Nonterminal(block)) {
                return (args, Block::new(child));
            }
        }
        unreachable!()
    }

    pub fn search_potential_self_assignments(&self) -> PotentialSelfAssignments<'db> {
        PotentialSelfAssignments(self.node.search(&[Nonterminal(t_primary)]))
    }
}

pub struct PotentialSelfAssignments<'db>(SearchIterator<'db>);

impl<'db> Iterator for PotentialSelfAssignments<'db> {
    type Item = (Name<'db>, Name<'db>);
    fn next(&mut self) -> Option<Self::Item> {
        for node in &mut self.0 {
            let name_def = node.nth_child(2);
            if name_def.is_type(Nonterminal(name_definition)) {
                let atom_ = node.nth_child(0);
                if atom_.is_type(Nonterminal(atom)) {
                    let self_name = atom_.nth_child(0);
                    if self_name.is_type(Terminal(TerminalType::Name)) {
                        return Some((Name::new(self_name), NameDefinition::new(name_def).name()));
                    }
                }
            }
        }
        None
    }
}

impl<'db> FunctionDef<'db> {
    pub fn name_definition(&self) -> NameDefinition<'db> {
        NameDefinition::new(self.node.nth_child(1))
    }

    pub fn name(&self) -> Name<'db> {
        self.name_definition().name()
    }

    pub fn from_param_name_def_index(tree: &'db Tree, param_name_index: NodeIndex) -> Self {
        Self::new(
            tree.0
                .node_by_index(param_name_index)
                .parent_until(&[Nonterminal(function_def)])
                .unwrap(),
        )
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation<'db>> {
        let ret = self.node.nth_child(3);
        if ret.is_type(Nonterminal(return_annotation)) {
            Some(ReturnAnnotation::new(ret))
        } else {
            None
        }
    }

    pub fn params(&self) -> FunctionDefParameters<'db> {
        FunctionDefParameters::new(self.node.nth_child(2))
    }

    pub fn parent(&self) -> FunctionParent<'db> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(stmt)) {
            FunctionParent::Normal
        } else if parent.is_type(Nonterminal(decorated)) {
            FunctionParent::Decorated(Decorated::new(parent))
        } else if parent.is_type(Nonterminal(async_stmt)) {
            FunctionParent::Async
        } else if parent.is_type(Nonterminal(async_function_def)) {
            FunctionParent::DecoratedAsync(Decorated::new(parent))
        } else {
            unreachable!()
        }
    }

    pub fn unpack(
        &self,
    ) -> (
        NameDefinition<'db>,
        FunctionDefParameters<'db>,
        Option<ReturnAnnotation<'db>>,
        Block<'db>,
    ) {
        // function_def: "def" name_definition function_def_parameters
        //               return_annotation? ":" block
        let mut iterator = self.node.iter_children();
        iterator.next();
        let name_def = NameDefinition::new(iterator.next().unwrap());
        let params = FunctionDefParameters::new(iterator.next().unwrap());
        let mut ret_annot = iterator.next();
        if ret_annot.unwrap().is_type(Nonterminal(return_annotation)) {
            iterator.next();
        } else {
            ret_annot = None;
        }
        (
            name_def,
            params,
            ret_annot.map(ReturnAnnotation::new),
            Block::new(iterator.next().unwrap()),
        )
    }
}

pub enum FunctionParent<'db> {
    Decorated(Decorated<'db>),
    Async,
    DecoratedAsync(Decorated<'db>),
    Normal,
}

impl<'db> FunctionDefParameters<'db> {
    pub fn iter(&self) -> ParamIterator<'db> {
        // function_def_parameters: "(" [parameters] ")"
        let params = self.node.nth_child(1);
        if params.is_type(Nonterminal(parameters)) {
            let positional_only = params
                .iter_children()
                .any(|n| n.is_leaf() && n.as_code() == "/");
            ParamIterator::Iterator(params.iter_children(), positional_only)
        } else {
            ParamIterator::Finished
        }
    }
}

pub enum ParamIterator<'db> {
    Iterator(SiblingIterator<'db>, bool),
    Finished,
}

impl<'db> Iterator for ParamIterator<'db> {
    type Item = Param<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Iterator(iterator, positional_only) => {
                for node in iterator {
                    use ParamType::*;
                    if node.is_type(Nonterminal(param_no_default))
                        || node.is_type(Nonterminal(param_with_default))
                    {
                        return Some(Self::Item::new(
                            &mut node.iter_children(),
                            if *positional_only {
                                PositionalOnly
                            } else {
                                PositionalOrKeyword
                            },
                        ));
                    } else if node.is_type(Nonterminal(star_etc)) {
                        *self = Self::Iterator(node.iter_children(), false);
                        return self.next();
                    } else if node.is_type(Nonterminal(param_maybe_default)) {
                        debug_assert!(!*positional_only);
                        return Some(Self::Item::new(&mut node.iter_children(), KeywordOnly));
                    } else if node.is_type(Nonterminal(starred_param)) {
                        return Some(Self::Item::new(&mut node.iter_children().skip(1), Starred));
                    } else if node.is_type(Nonterminal(double_starred_param)) {
                        return Some(Self::Item::new(
                            &mut node.iter_children().skip(1),
                            DoubleStarred,
                        ));
                    }
                }
                None
            }
            Self::Finished => None,
        }
    }
}

#[derive(Debug)]
pub struct Param<'db> {
    type_: ParamType,
    name_def: NameDefinition<'db>,
    annotation: Option<Annotation<'db>>,
    default: Option<Expression<'db>>,
}

impl<'db> Param<'db> {
    fn new(param_children: &mut impl Iterator<Item = PyNode<'db>>, type_: ParamType) -> Self {
        let name_def = NameDefinition::new(param_children.next().unwrap());
        let annot = param_children.next().and_then(|n| {
            if n.is_type(Nonterminal(annotation)) {
                Some(Annotation::new(n))
            } else {
                None
            }
        });
        param_children.next();
        let default_node = param_children.next();
        Self {
            type_,
            name_def,
            annotation: annot,
            default: default_node.map(Expression::new),
        }
    }

    pub fn type_(&self) -> ParamType {
        self.type_
    }

    pub fn default(&self) -> Option<Expression<'db>> {
        self.default
    }

    pub fn name_definition(&self) -> NameDefinition<'db> {
        self.name_def
    }

    pub fn annotation(&self) -> Option<Annotation<'db>> {
        self.annotation
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ParamType {
    PositionalOnly,
    PositionalOrKeyword,
    KeywordOnly,
    Starred,
    DoubleStarred,
}

pub enum SimpleParamType {
    Normal,
    MultiArgs,
    MultiKwargs,
}

impl<'db> Annotation<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> ReturnAnnotation<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ArgumentsDetails<'db> {
    None,
    Comprehension(Comprehension<'db>),
    Node(Arguments<'db>),
}

impl<'db> Assignment<'db> {
    pub fn unpack(&self) -> AssignmentContent<'db> {
        // | (star_targets "=" )+ (yield_expr | star_expressions)
        // | single_target annotation ["=" (yield_expr | star_expressions)]
        // | single_target augassign (yield_expr | star_expressions)
        let mut iterator = self.node.iter_children().skip(1);
        while let Some(child) = iterator.next() {
            if child.is_type(Nonterminal(yield_expr))
                || child.is_type(Nonterminal(star_expressions))
            {
                let iter = AssignmentTargetIterator(self.node.iter_children().step_by(2));
                return AssignmentContent::Normal(iter, Self::right_side(child));
            } else if child.is_type(Nonterminal(annotation)) {
                iterator.next();
                let right = iterator.next().map(Self::right_side);
                return AssignmentContent::WithAnnotation(
                    Target::new_single_target(self.node.nth_child(0)),
                    Annotation::new(child),
                    right,
                );
            } else if child.is_type(Nonterminal(augassign)) {
                let right = Self::right_side(iterator.next().unwrap());
                return AssignmentContent::AugAssign(
                    Target::new_single_target(self.node.nth_child(0)),
                    AugAssign::new(child),
                    right,
                );
            }
        }
        unreachable!()
    }

    pub fn unpack_with_simple_targets(&self) -> AssignmentContentWithSimpleTargets<'db> {
        // | (star_targets "=" )+ (yield_expr | star_expressions)
        // | single_target annotation ["=" (yield_expr | star_expressions)]
        // | single_target augassign (yield_expr | star_expressions)
        let mut iterator = self.node.iter_children().skip(1);
        while let Some(child) = iterator.next() {
            if child.is_type(Nonterminal(yield_expr))
                || child.is_type(Nonterminal(star_expressions))
            {
                let iter = StarTargetsIterator(self.node.iter_children().step_by(2));
                return AssignmentContentWithSimpleTargets::Normal(iter, Self::right_side(child));
            } else if child.is_type(Nonterminal(annotation)) {
                iterator.next();
                let right = iterator.next().map(Self::right_side);
                return AssignmentContentWithSimpleTargets::WithAnnotation(
                    SingleTarget::new(self.node.nth_child(0)),
                    Annotation::new(child),
                    right,
                );
            } else if child.is_type(Nonterminal(augassign)) {
                let right = Self::right_side(iterator.next().unwrap());
                return AssignmentContentWithSimpleTargets::AugAssign(
                    SingleTarget::new(self.node.nth_child(0)),
                    AugAssign::new(child),
                    right,
                );
            }
        }
        unreachable!()
    }

    fn right_side(child: PyNode) -> AssignmentRightSide {
        if child.is_type(Nonterminal(star_expressions)) {
            return AssignmentRightSide::StarExpressions(StarExpressions::new(child));
        } else {
            return AssignmentRightSide::YieldExpr(YieldExpr::new(child));
        }
    }

    pub fn maybe_simple_type_expression_assignment(&self) -> Option<Expression<'db>> {
        match self.unpack() {
            AssignmentContent::Normal(mut targets_, right) => {
                targets_.next();
                if targets_.next().is_some() {
                    return None;
                }

                if let AssignmentRightSide::StarExpressions(star_exprs) = right {
                    if let StarExpressionContent::Expression(expr) = star_exprs.unpack() {
                        return Some(expr);
                    }
                }
                None
            }
            AssignmentContent::WithAnnotation(_, _, _) => todo!(),
            AssignmentContent::AugAssign(_, _, _) => None,
        }
    }

    pub fn maybe_simple_type_reassignment(&self) -> Option<Name<'db>> {
        self.maybe_simple_type_expression_assignment()
            .and_then(|expr| expr.maybe_name_or_last_primary_name())
    }
}

pub enum AssignmentContent<'db> {
    Normal(AssignmentTargetIterator<'db>, AssignmentRightSide<'db>),
    WithAnnotation(
        Target<'db>,
        Annotation<'db>,
        Option<AssignmentRightSide<'db>>,
    ),
    AugAssign(Target<'db>, AugAssign<'db>, AssignmentRightSide<'db>),
}

pub enum AssignmentContentWithSimpleTargets<'db> {
    Normal(StarTargetsIterator<'db>, AssignmentRightSide<'db>),
    WithAnnotation(
        SingleTarget<'db>,
        Annotation<'db>,
        Option<AssignmentRightSide<'db>>,
    ),
    AugAssign(SingleTarget<'db>, AugAssign<'db>, AssignmentRightSide<'db>),
}

pub enum AssignmentRightSide<'db> {
    YieldExpr(YieldExpr<'db>),
    StarExpressions(StarExpressions<'db>),
}

pub struct StarTargetsIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for StarTargetsIterator<'db> {
    type Item = StarTargets<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.0.next() {
            if node.is_type(Nonterminal(star_targets)) {
                return Some(StarTargets::new(node));
            }
        }
        None
    }
}

pub struct AssignmentTargetIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for AssignmentTargetIterator<'db> {
    type Item = Target<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.0.next() {
            if node.is_type(Nonterminal(star_targets)) {
                return Some(Target::new(node));
            }
        }
        None
    }
}

impl<'db> ImportFrom<'db> {
    pub fn level_with_dotted_name(&self) -> (usize, Option<DottedName<'db>>) {
        // | "from" ("." | "...")* dotted_name "import" import_from_targets
        // | "from" ("." | "...")+ "import" import_from_targets
        let mut level = 0;
        for node in self.node.iter_children().skip(1) {
            if node.is_type(Nonterminal(dotted_name)) {
                return (level, Some(DottedName::new(node)));
            } else if node.as_code() == "." {
                level += 1;
            } else if node.as_code() == "..." {
                level += 3;
            } else if node.as_code() == "import" {
                break;
            }
        }
        (level, None)
    }

    pub fn unpack_targets(&self) -> ImportFromTargets<'db> {
        // import_from_targets:
        //     "*" | "(" ",".import_from_as_name+ ","? ")" | ",".import_from_as_name+
        for node in self.node.iter_children().skip(3) {
            if node.is_type(Nonterminal(import_from_targets)) {
                let first = node.nth_child(0);
                if first.is_leaf() && first.as_code() == "*" {
                    return ImportFromTargets::Star(Keyword::new(first));
                } else {
                    return ImportFromTargets::Iterator(ImportFromTargetsIterator(
                        node.iter_children(),
                    ));
                }
            }
        }
        unreachable!()
    }
}

pub enum ImportFromTargets<'db> {
    Star(Keyword<'db>),
    Iterator(ImportFromTargetsIterator<'db>),
}

pub struct ImportFromTargetsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ImportFromTargetsIterator<'db> {
    type Item = ImportFromAsName<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for child in &mut self.0 {
            if child.is_type(Nonterminal(import_from_as_name)) {
                // import_from_as_name: Name "as" name_definition | name_definition
                return Some(ImportFromAsName::new(child));
            }
        }
        None
    }
}

impl<'db> ImportFromAsName<'db> {
    pub fn name_definition(&self) -> NameDefinition {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(name_definition)) {
            NameDefinition::new(first)
        } else {
            NameDefinition::new(self.node.nth_child(2))
        }
    }

    pub fn unpack(&self) -> (Name<'db>, NameDefinition<'db>) {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(name_definition)) {
            let name_def = NameDefinition::new(first);
            (name_def.name(), name_def)
        } else {
            // foo as bar
            let def = first.next_sibling().unwrap().next_sibling().unwrap();
            (Name::new(first), NameDefinition::new(def))
        }
    }
}

impl<'db> DottedName<'db> {
    pub fn unpack(&self) -> DottedNameContent<'db> {
        let mut children = self.node.iter_children();
        let first = children.next().unwrap();
        if first.is_type(Terminal(TerminalType::Name)) {
            DottedNameContent::Name(Name::new(first))
        } else {
            children.next();
            let name = children.next().unwrap();
            DottedNameContent::DottedName(DottedName::new(first), Name::new(name))
        }
    }
}

pub enum DottedNameContent<'db> {
    DottedName(DottedName<'db>, Name<'db>),
    Name(Name<'db>),
}

impl<'db> ImportName<'db> {
    pub fn iter_dotted_as_names(&self) -> DottedAsNameIterator<'db> {
        DottedAsNameIterator(self.node.nth_child(1).iter_children())
    }
}

pub struct DottedAsNameIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for DottedAsNameIterator<'db> {
    type Item = DottedAsName<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let result = self.0.next();
        if result.is_some() {
            self.0.next();
        }
        result.map(Self::Item::new)
    }
}

pub enum DottedAsNameContent<'db> {
    Simple(NameDefinition<'db>, Option<DottedName<'db>>),
    WithAs(DottedName<'db>, NameDefinition<'db>),
}

impl<'db> DottedAsName<'db> {
    #[inline]
    pub fn unpack(&self) -> DottedAsNameContent<'db> {
        let first = self.node.nth_child(0);
        let maybe_second = first.next_sibling();
        if first.is_type(Nonterminal(name_definition)) {
            DottedAsNameContent::Simple(
                NameDefinition::new(first),
                maybe_second.map(|s| DottedName::new(s.next_sibling().unwrap())),
            )
        } else {
            DottedAsNameContent::WithAs(
                DottedName::new(first),
                NameDefinition::new(maybe_second.unwrap().next_sibling().unwrap()),
            )
        }
    }
}

impl<'db> PrimaryTarget<'db> {
    pub fn first(&self) -> PrimaryTargetOrAtom<'db> {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(atom)) {
            PrimaryTargetOrAtom::Atom(Atom::new(first))
        } else {
            PrimaryTargetOrAtom::PrimaryTarget(PrimaryTarget::new(first))
        }
    }

    pub fn second(&self) -> PrimaryContent<'db> {
        let second = self.node.nth_child(2);
        if second.is_type(Nonterminal(name_definition)) {
            PrimaryContent::Attribute(Name::new(second.nth_child(0)))
        } else if second.is_type(Nonterminal(arguments)) {
            PrimaryContent::Execution(ArgumentsDetails::Node(Arguments::new(second)))
        } else if second.is_type(Nonterminal(named_expression)) {
            PrimaryContent::GetItem(SliceType::NamedExpression(NamedExpression::new(second)))
        } else if second.is_type(Nonterminal(comprehension)) {
            PrimaryContent::Execution(ArgumentsDetails::Comprehension(Comprehension::new(second)))
        } else if second.is_type(Nonterminal(slice)) {
            PrimaryContent::GetItem(SliceType::Slice(Slice::new(second)))
        } else if second.is_type(Nonterminal(slices)) {
            PrimaryContent::GetItem(SliceType::Slices(Slices::new(second)))
        } else {
            debug_assert_eq!(second.as_code(), ")");
            PrimaryContent::Execution(ArgumentsDetails::None)
        }
    }
}

impl<'db> Primary<'db> {
    pub fn first(&self) -> PrimaryOrAtom<'db> {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(atom)) {
            PrimaryOrAtom::Atom(Atom::new(first))
        } else {
            debug_assert_eq!(first.type_(), Nonterminal(primary));
            PrimaryOrAtom::Primary(Primary::new(first))
        }
    }

    pub fn second(&self) -> PrimaryContent<'db> {
        let second = self.node.nth_child(2);
        if second.is_type(Terminal(TerminalType::Name)) {
            PrimaryContent::Attribute(Name::new(second))
        } else if second.is_type(Nonterminal(arguments)) {
            PrimaryContent::Execution(ArgumentsDetails::Node(Arguments::new(second)))
        } else if second.is_type(Nonterminal(named_expression)) {
            PrimaryContent::GetItem(SliceType::NamedExpression(NamedExpression::new(second)))
        } else if second.is_type(Nonterminal(comprehension)) {
            PrimaryContent::Execution(ArgumentsDetails::Comprehension(Comprehension::new(second)))
        } else if second.is_type(Nonterminal(slice)) {
            PrimaryContent::GetItem(SliceType::Slice(Slice::new(second)))
        } else if second.is_type(Nonterminal(slices)) {
            PrimaryContent::GetItem(SliceType::Slices(Slices::new(second)))
        } else {
            debug_assert_eq!(second.as_code(), ")");
            PrimaryContent::Execution(ArgumentsDetails::None)
        }
    }

    pub fn expect_slice(&self) -> SliceType<'db> {
        let second = self.node.nth_child(2);
        if second.is_type(Nonterminal(named_expression)) {
            SliceType::NamedExpression(NamedExpression::new(second))
        } else if second.is_type(Nonterminal(slice)) {
            SliceType::Slice(Slice::new(second))
        } else {
            SliceType::Slices(Slices::new(second))
        }
    }

    pub fn parent(&self) -> PrimaryParent<'db> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(t_primary)) {
            PrimaryParent::Primary(Primary::new(parent))
        } else {
            PrimaryParent::Other
        }
    }

    fn is_only_attributes(&self) -> Option<Name<'db>> {
        match self.first() {
            PrimaryOrAtom::Atom(_) => (),
            PrimaryOrAtom::Primary(p) => {
                p.is_only_attributes()?;
            }
        }
        match self.second() {
            PrimaryContent::Attribute(name) => Some(name),
            _ => None,
        }
    }
}

pub enum PrimaryParent<'db> {
    Primary(Primary<'db>),
    Other,
}

impl<'db> BitwiseOr<'db> {
    pub fn unpack(&self) -> (ExpressionPart<'db>, ExpressionPart<'db>) {
        // TODO this is probably unused
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();
        iter.next();
        let third = iter.next().unwrap();
        (ExpressionPart::new(first), ExpressionPart::new(third))
    }
}

pub struct Operation<'db> {
    pub left: ExpressionPart<'db>,
    pub magic_method: &'static str,
    pub reverse_magic_method: &'static str,
    pub operand: &'static str,
    pub right: ExpressionPart<'db>,
    pub index: NodeIndex,
}

impl<'db> Operation<'db> {
    fn new(
        node: PyNode<'db>,
        magic_method: &'static str,
        reverse_magic_method: &'static str,
        operand: &'static str,
    ) -> Self {
        let mut iter = node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        iter.next();
        let right = ExpressionPart::new(iter.next().unwrap());
        Self {
            left,
            magic_method,
            reverse_magic_method,
            operand,
            right,
            index: node.index,
        }
    }
}

impl<'db> AugAssign<'db> {
    pub fn magic_methods(&self) -> (&'static str, &'static str, &'static str) {
        let code = self.node.as_code();
        match code.as_bytes().get(0).unwrap() {
            b'+' => ("__iadd__", "__add__", "__radd__"),
            b'-' => ("__isub__", "__sub__", "__rsub__"),
            b'*' => {
                if code.as_bytes().get(1).unwrap() == &b'*' {
                    ("__ipow__", "__pow__", "__rpow__")
                } else {
                    ("__imul__", "__mul__", "__rmul__")
                }
            }
            b'/' => {
                if code.as_bytes().get(1).unwrap() == &b'/' {
                    ("__itruediv__", "__truediv__", "__rtruediv__")
                } else {
                    ("__idiv__", "__div__", "__rdiv__")
                }
            }
            b'%' => ("__imod__", "__mod__", "__rmod__"),
            b'&' => ("__iand__", "__and__", "__rand__"),
            b'|' => ("__ior__", "__or__", "__ror__"),
            b'^' => ("__ixor__", "__xor__", "__rxor__"),
            b'<' => ("__ilshift__", "__lshift__", "__rlshift__"),
            b'>' => ("__irshift__", "__rshift__", "__rrshift__"),
            b'@' => ("__imatmul__", "__matmul__", "__rmatmul__"),
            _ => unreachable!(),
        }
    }

    pub fn operand(&self) -> &'db str {
        // For example: += -> +
        let s = self.node.as_code();
        from_utf8(&s.as_bytes()[..s.len() - 1]).unwrap()
    }
}

impl<'db> Sum<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let op = iter.next().unwrap().as_code();
        let right = ExpressionPart::new(iter.next().unwrap());
        let (magic_method, reverse_magic_method, operand) = if op == "+" {
            ("__add__", "__radd__", "+")
        } else {
            debug_assert_eq!(op, "-");
            ("__sub__", "__rsub__", "-")
        };
        Operation {
            left,
            magic_method,
            reverse_magic_method,
            operand,
            right,
            index: self.node.index,
        }
    }
}

impl<'db> Term<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let op = iter.next().unwrap().as_code();
        let right = ExpressionPart::new(iter.next().unwrap());
        let (magic_method, reverse_magic_method, operand) = if op == "*" {
            ("__mul__", "__rmul__", "+")
        } else if op == "/" {
            ("__truediv__", "__rtruediv__", "/")
        } else if op == "//" {
            ("__floordiv__", "__rfloordiv__", "//")
        } else if op == "%" {
            ("__mod__", "__rmod__", "%")
        } else {
            debug_assert_eq!(op, "%");
            ("__matmul__", "__rmatmul__", "%")
        };
        Operation {
            left,
            magic_method,
            reverse_magic_method,
            operand,
            right,
            index: self.node.index,
        }
    }
}

impl<'db> BitwiseOr<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        Operation::new(self.node, "__add__", "__radd__", "+")
    }
}

impl<'db> Disjunction<'db> {
    pub fn unpack(&self) -> (ExpressionPart<'db>, ExpressionPart<'db>) {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let _operand = iter.next().unwrap();
        (left, ExpressionPart::new(iter.next().unwrap()))
    }
}

pub enum ComparisonContent<'db> {
    Equals(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    NotEquals(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    Is(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    IsNot(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    In(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    NotIn(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    Operation(Operation<'db>),
}

impl<'db> Comparison<'db> {
    pub fn unpack(&self) -> ComparisonContent<'db> {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let operand = iter.next().unwrap();
        let first_operand = operand.nth_child(0);
        let right = ExpressionPart::new(iter.next().unwrap());
        let (magic_method, reverse_magic_method, operand) = match first_operand.as_code() {
            "==" => return ComparisonContent::Equals(left, Operand::new(operand), right),
            "!=" => return ComparisonContent::NotEquals(left, Operand::new(operand), right),
            "is" => {
                if let Some(s) = first_operand.next_sibling() {
                    debug_assert_eq!(s.as_code(), "not");
                    return ComparisonContent::IsNot(left, Operand::new(operand), right);
                } else {
                    return ComparisonContent::Is(left, Operand::new(operand), right);
                }
            }
            "<" => ("__lt__", "__gt__", "<"),
            ">" => ("__gt__", "__lt__", ">"),
            "<=" => ("__le__", "__ge__", "<="),
            ">=" => ("__ge__", "__le__", ">="),
            "in" => return ComparisonContent::In(left, Operand::new(operand), right),
            "not" => return ComparisonContent::NotIn(left, Operand::new(operand), right),
            _ => unreachable!(),
        };
        ComparisonContent::Operation(Operation {
            left,
            magic_method,
            reverse_magic_method,
            operand,
            right,
            index: self.node.index,
        })
    }
}

pub enum PrimaryOrAtom<'db> {
    Primary(Primary<'db>),
    Atom(Atom<'db>),
}

pub enum PrimaryTargetOrAtom<'db> {
    PrimaryTarget(PrimaryTarget<'db>),
    Atom(Atom<'db>),
}

#[derive(Debug)]
pub enum PrimaryContent<'db> {
    Attribute(Name<'db>),
    Execution(ArgumentsDetails<'db>),
    GetItem(SliceType<'db>),
}

#[derive(Clone, Copy, Debug)]
pub enum SliceType<'db> {
    Slices(Slices<'db>),
    Slice(Slice<'db>),
    NamedExpression(NamedExpression<'db>),
}

impl<'db> Slices<'db> {
    pub fn iter(&self) -> SliceIterator<'db> {
        SliceIterator(self.node.iter_children())
    }
}

#[derive(Clone, Copy)]
pub enum SliceContent<'db> {
    Slice(Slice<'db>),
    NamedExpression(NamedExpression<'db>),
}

pub struct SliceIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for SliceIterator<'db> {
    type Item = SliceContent<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let result = self.0.next().map(|n| {
            if n.is_type(Nonterminal(slices)) {
                SliceContent::Slice(Slice::new(n))
            } else {
                SliceContent::NamedExpression(NamedExpression::new(n))
            }
        });
        self.0.next();
        result
    }
}

impl<'db> Arguments<'db> {
    pub fn iter(&self) -> ArgumentsIterator<'db> {
        ArgumentsIterator(self.node.iter_children())
    }

    pub fn search_names(&self) -> NameIterator<'db> {
        NameIterator(self.node.search(&[Terminal(TerminalType::Name)]))
    }
}

pub struct NameIterator<'db>(SearchIterator<'db>);

impl<'db> Iterator for NameIterator<'db> {
    type Item = Name<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Name::new)
    }
}

#[derive(Debug)]
pub struct ArgumentsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ArgumentsIterator<'db> {
    type Item = Argument<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for node in &mut self.0 {
            if node.is_type(Nonterminal(named_expression)) {
                return Some(Argument::Positional(NamedExpression::new(node)));
            } else if node.is_type(Nonterminal(kwargs)) {
                *self = Self(node.iter_children());
                return self.next();
            } else if node.is_type(Nonterminal(kwarg)) {
                // kwarg: Name "=" expression
                let mut kwarg_iterator = node.iter_children();
                let name = kwarg_iterator.next().unwrap().as_code();
                kwarg_iterator.next();
                let arg = kwarg_iterator.next().unwrap();
                return Some(Argument::Keyword(name, Expression::new(arg)));
            } else if node.is_type(Nonterminal(starred_expression)) {
                return Some(Argument::Starred(Expression::new(node.nth_child(1))));
            } else if node.is_type(Nonterminal(double_starred_expression)) {
                return Some(Argument::DoubleStarred(Expression::new(node.nth_child(1))));
            }
        }
        None
    }
}

#[derive(Debug)]
pub enum Argument<'db> {
    Positional(NamedExpression<'db>),
    Keyword(&'db str, Expression<'db>),
    Starred(Expression<'db>),
    DoubleStarred(Expression<'db>),
}

pub enum ReturnOrYield<'db> {
    Return(ReturnStmt<'db>),
    Yield(YieldExpr<'db>),
}

impl<'db> ReturnOrYield<'db> {
    #[inline]
    pub fn by_index(tree: &'db Tree, index: NodeIndex) -> Self {
        let node = tree.0.node_by_index(index);
        if node.is_type(Nonterminal(return_stmt)) {
            ReturnOrYield::Return(ReturnStmt::new(node))
        } else {
            ReturnOrYield::Yield(YieldExpr::new(node))
        }
    }
}

impl<'db> ReturnStmt<'db> {
    pub fn star_expressions(&self) -> StarExpressions<'db> {
        StarExpressions::new(self.node.nth_child(1))
    }
}

impl<'db> YieldExpr<'db> {
    pub fn unpack(&self) -> YieldExprContent<'db> {
        let node = self.node.nth_child(1);
        if node.is_type(Nonterminal(star_expressions)) {
            YieldExprContent::StarExpressions(StarExpressions::new(node))
        } else {
            YieldExprContent::YieldFrom(YieldFrom::new(node))
        }
    }
}

pub enum YieldExprContent<'db> {
    StarExpressions(StarExpressions<'db>),
    YieldFrom(YieldFrom<'db>),
}

impl<'db> Lambda<'db> {
    fn calculate_param_iterator(lambda_param_node: &PyNode<'db>) -> ParamIterator<'db> {
        if lambda_param_node.is_type(Nonterminal(lambda_parameters)) {
            let positional_only = lambda_param_node
                .iter_children()
                .any(|n| n.is_leaf() && n.as_code() == "/");
            ParamIterator::Iterator(lambda_param_node.iter_children(), positional_only)
        } else {
            ParamIterator::Finished
        }
    }

    pub fn params(&self) -> ParamIterator<'db> {
        let n = self.node.nth_child(1);
        Self::calculate_param_iterator(&n)
    }

    pub fn unpack(&self) -> (ParamIterator<'db>, Expression<'db>) {
        // "lambda" [lambda_parameters] ":" expression
        let mut iterator = self.node.iter_children().skip(1);
        let params = Self::calculate_param_iterator(&iterator.next().unwrap());
        if let ParamIterator::Iterator(_, _) = params {
            iterator.next();
        }
        (params, Expression::new(iterator.next().unwrap()))
    }
}

impl<'db> NameDefinition<'db> {
    #[inline]
    pub fn name(&self) -> Name<'db> {
        Name::new(self.node.nth_child(0))
    }

    pub fn name_index(&self) -> NodeIndex {
        debug_assert!(self.name().index() == self.index() + 1);
        self.index() + 1
    }

    pub fn is_not_primary(&self) -> bool {
        !self.node.parent().unwrap().is_type(Nonterminal(t_primary))
    }

    pub fn expect_stmt_like_ancestor(&self) -> StmtLike<'db> {
        let stmt_node = self
            .node
            .parent_until(&[
                Nonterminal(stmt),
                Nonterminal(lambda),
                Nonterminal(comprehension),
                Nonterminal(dict_comprehension),
            ])
            .expect("There should always be a stmt");
        if stmt_node.is_type(Nonterminal(stmt)) {
            StmtLike::Stmt(Stmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(lambda)) {
            StmtLike::Lambda(Lambda::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(comprehension)) {
            StmtLike::Comprehension(Comprehension::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(dict_comprehension)) {
            StmtLike::DictComprehension(DictComprehension::new(stmt_node))
        } else {
            unreachable!()
        }
    }

    pub fn maybe_primary_parent(&self) -> Option<Primary<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(primary)) {
            Some(Primary::new(parent))
        } else {
            None
        }
    }

    pub fn function_or_lambda_ancestor(&self) -> Option<FunctionOrLambda<'db>> {
        self.node
            .parent_until(&[Nonterminal(function_def), Nonterminal(lambda)])
            .map(|node| {
                if node.is_type(Nonterminal(function_def)) {
                    FunctionOrLambda::Function(FunctionDef::new(node))
                } else {
                    debug_assert_eq!(node.type_(), Nonterminal(lambda));
                    FunctionOrLambda::Lambda(Lambda::new(node))
                }
            })
    }

    pub fn maybe_param_annotation(&self) -> Option<Annotation<'db>> {
        if let Some(next) = self.node.next_sibling() {
            if next.is_type(Nonterminal(annotation)) {
                return Some(Annotation::new(next));
            }
        }
        None
    }
}

impl<'db> Atom<'db> {
    #[inline]
    pub fn unpack(&self) -> AtomContent<'db> {
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();

        match first.type_() {
            Terminal(TerminalType::Name) => AtomContent::Name(Name::new(first)),
            Terminal(TerminalType::Number) => {
                let code = first.as_code();
                if code.contains('j') {
                    AtomContent::Complex(Complex::new(first))
                } else if code.contains('.') {
                    AtomContent::Float(Float::new(first))
                } else {
                    AtomContent::Int(Int::new(first))
                }
            }
            Nonterminal(strings) => AtomContent::StringsOrBytes(StringsOrBytes::new(first)),
            PyNodeType::Keyword => match first.as_code() {
                "None" => AtomContent::NoneLiteral,
                "True" | "False" => AtomContent::Boolean(Keyword::new(first)),
                "..." => AtomContent::Ellipsis,
                "(" => {
                    let next_node = iter.next().unwrap();
                    match next_node.type_() {
                        Nonterminal(tuple_content) => AtomContent::Tuple(Tuple::new(self.node)),
                        Nonterminal(yield_expr) => {
                            AtomContent::YieldExpr(YieldExpr::new(next_node))
                        }
                        Nonterminal(named_expression) => {
                            AtomContent::NamedExpression(NamedExpression::new(next_node))
                        }
                        Nonterminal(comprehension) => {
                            AtomContent::GeneratorComprehension(Comprehension::new(next_node))
                        }
                        PyNodeType::Keyword => {
                            debug_assert_eq!(next_node.as_code(), ")");
                            AtomContent::Tuple(Tuple::new(self.node))
                        }
                        _ => unreachable!(),
                    }
                }
                "[" => {
                    let next_node = iter.next().unwrap();
                    if next_node.is_type(Nonterminal(comprehension)) {
                        AtomContent::ListComprehension(Comprehension::new(next_node))
                    } else {
                        AtomContent::List(List::new(self.node))
                    }
                }
                "{" => {
                    let next_node = iter.next().unwrap();
                    match next_node.type_() {
                        Nonterminal(dict_content) => AtomContent::Dict(Dict::new(self.node)),
                        Nonterminal(dict_comprehension) => {
                            AtomContent::DictComprehension(DictComprehension::new(next_node))
                        }
                        Nonterminal(star_named_expressions) => {
                            AtomContent::Set(Set::new(self.node))
                        }
                        Nonterminal(comprehension) => {
                            AtomContent::SetComprehension(Comprehension::new(next_node))
                        }
                        PyNodeType::Keyword => {
                            debug_assert_eq!(next_node.as_code(), "}");
                            AtomContent::Dict(Dict::new(self.node))
                        }
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}

pub enum AtomContent<'db> {
    Name(Name<'db>),

    Float(Float<'db>),
    Int(Int<'db>),
    Complex(Complex<'db>),
    StringsOrBytes(StringsOrBytes<'db>),

    NoneLiteral,
    Boolean(Keyword<'db>),
    Ellipsis,

    List(List<'db>),
    ListComprehension(Comprehension<'db>),
    Dict(Dict<'db>),
    DictComprehension(DictComprehension<'db>),
    Set(Set<'db>),
    SetComprehension(Comprehension<'db>),
    Tuple(Tuple<'db>),
    GeneratorComprehension(Comprehension<'db>),
    YieldExpr(YieldExpr<'db>),
    NamedExpression(NamedExpression<'db>),
}

impl<'db> PyString<'db> {
    pub fn content(&self) -> &'db str {
        let code = self.node.as_code();
        let bytes = code.as_bytes();
        let mut start = 0;
        let mut quote = None;
        for (i, b) in bytes.iter().enumerate() {
            if *b == b'"' || *b == b'\'' {
                if let Some(quote) = quote {
                    if *b == quote && i == start + 3 {
                        return &code[start + 3..code.len() - 3];
                    }
                    break;
                } else {
                    quote = Some(*b);
                }
            } else if quote.is_some() {
                break;
            } else {
                start += 1;
            }
        }
        &code[start + 1..code.len() - 1]
    }
}

impl<'db> StringsOrBytes<'db> {
    pub fn as_python_string(&self) -> Option<PythonString<'db>> {
        PythonString::new(self.node.iter_children())
    }

    pub fn iter(&self) -> StringOrByteIterator<'db> {
        StringOrByteIterator(self.node.iter_children())
    }

    pub fn maybe_single_string_literal(&self) -> Option<PyString<'db>> {
        let mut iterator = self.iter();
        if let Some(StringOrByte::String(s)) = iterator.next() {
            Some(s)
        } else {
            None
        }
    }
}

pub struct StringOrByteIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for StringOrByteIterator<'db> {
    type Item = StringOrByte<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| {
            if n.is_type(Nonterminal(fstring)) {
                StringOrByte::FString(FString::new(n))
            } else if starts_with_string(&n) {
                StringOrByte::String(PyString::new(n))
            } else {
                StringOrByte::Bytes(Bytes::new(n))
            }
        })
    }
}

pub enum StringOrByte<'db> {
    String(PyString<'db>),
    Bytes(Bytes<'db>),
    FString(FString<'db>),
}

impl<'db> FString<'db> {
    pub fn iter_content(&self) -> impl Iterator<Item = FStringContent<'db>> {
        FStringContentIterator(self.node.iter_children().skip(1))
    }
}

pub struct FStringContentIterator<'db>(Skip<SiblingIterator<'db>>);

impl<'db> Iterator for FStringContentIterator<'db> {
    type Item = FStringContent<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().and_then(|n| {
            if n.is_type(Nonterminal(fstring_expr)) {
                Some(Self::Item::FStringExpr(FStringExpr::new(n)))
            } else if n.is_type(Terminal(TerminalType::FStringEnd)) {
                None
            } else {
                Some(Self::Item::FStringString(FStringString::new(n)))
            }
        })
    }
}

pub enum FStringContent<'db> {
    FStringString(FStringString<'db>),
    FStringExpr(FStringExpr<'db>),
}

impl<'db> FStringExpr<'db> {
    pub fn unpack(&self) -> (StarExpressions<'db>, Option<FStringFormatSpec<'db>>) {
        let mut iterator = self.node.iter_children().skip(1);
        // This is actually an `expressions` node, but `star_expressions` is a super set.
        let exprs = StarExpressions {
            node: iterator.next().unwrap(),
        };
        let format_spec = iterator
            .find(|n| n.is_type(Nonterminal(fstring_format_spec)))
            .map(FStringFormatSpec::new);
        (exprs, format_spec)
    }
}

impl<'db> FStringFormatSpec<'db> {
    pub fn iter_content(&self) -> impl Iterator<Item = FStringContent<'db>> {
        FStringContentIterator(self.node.iter_children().skip(1))
    }
}

pub enum NameOrKeywordLookup<'db> {
    Name(Name<'db>),
    Keyword(Keyword<'db>),
    None,
}

#[derive(Debug)]
pub enum Target<'db> {
    Tuple(TargetIterator<'db>),
    Name(NameDefinition<'db>),
    NameExpression(PrimaryTarget<'db>, NameDefinition<'db>),
    IndexExpression(PrimaryTarget<'db>),
    Starred(StarTarget<'db>),
}

impl<'db> Target<'db> {
    fn new(node: PyNode<'db>) -> Self {
        // star_targets: ",".star_target+ [","]
        // star_target:? "*"? (t_primary | star_target_brackets | name_definition)
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            Self::new_non_iterator(first)
        } else {
            debug_assert!(matches!(
                node.type_(),
                Nonterminal(star_targets) | Nonterminal(targets)
            ));
            Self::Tuple(TargetIterator(node.iter_children().step_by(2)))
        }
    }

    fn new_non_iterator(node: PyNode<'db>) -> Self {
        if node.is_type(Nonterminal(name_definition)) {
            Self::Name(NameDefinition::new(node))
        } else if node.is_type(Nonterminal(t_primary)) {
            Self::new_t_primary(node)
        } else if node.is_type(Nonterminal(star_target_brackets)) {
            // StarredTuple()
            todo!("star_target_brackets")
        } else if node.is_type(Nonterminal(star_target)) {
            Self::Starred(StarTarget::new(node))
        } else {
            unreachable!();
        }
    }

    fn new_t_primary(t_prim: PyNode<'db>) -> Self {
        t_prim
            .iter_children()
            .find(|x| x.is_type(Nonterminal(name_definition)))
            .map(|name_def| {
                Self::NameExpression(PrimaryTarget::new(t_prim), NameDefinition::new(name_def))
            })
            .unwrap_or_else(|| Self::IndexExpression(PrimaryTarget::new(t_prim)))
    }

    fn new_single_target(node: PyNode<'db>) -> Self {
        debug_assert_eq!(node.type_(), Nonterminal(single_target));

        // t_primary | name_definition | "(" single_target ")"
        let first = node.nth_child(0);
        if first.is_type(Nonterminal(name_definition)) {
            Self::Name(NameDefinition::new(first))
        } else if first.is_type(Nonterminal(t_primary)) {
            Self::new_t_primary(first)
        } else {
            debug_assert_eq!(node.nth_child(0).as_code(), "(");
            Self::new_single_target(first.nth_child(1))
        }
    }
}

impl<'db> NameOrKeywordLookup<'db> {
    pub fn from_position(tree: &'db Tree, position: CodeIndex) -> Self {
        // First check the token left and right of the cursor
        let mut left = tree.0.leaf_by_position(position);
        let mut right = left;
        if left.start() == position {
            if let Some(n) = left.previous_leaf() {
                if n.end() == position {
                    left = n;
                }
            }
        } else if left.end() == position {
            if let Some(n) = left.next_leaf() {
                if n.start() == position {
                    right = n;
                }
            }
        }
        // From now on left is the node we're passing.
        if left.index != right.index {
            use TerminalType::*;
            let order = [
                Name,
                Number,
                String,
                Bytes,
                FStringString,
                FStringStart,
                FStringEnd,
            ];
            match left.type_() {
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                    match right.type_() {
                        PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                            let is_alpha =
                                |n: PyNode| n.as_code().chars().all(|x| x.is_alphanumeric());
                            if is_alpha(right) && !is_alpha(left) {
                                // Prefer keywords to operators
                                left = right;
                            }
                        }
                        Terminal(t) | ErrorTerminal(t) => {
                            // If it is any of the wanted types, just use that instead.
                            if order.contains(&t) {
                                left = right;
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                Terminal(left_terminal) | ErrorTerminal(left_terminal) => {
                    match right.type_() {
                        Terminal(right_terminal) | ErrorTerminal(right_terminal) => {
                            let order_func = |type_| {
                                order.iter().position(|&t| t == type_).unwrap_or(usize::MAX)
                            };
                            let left_index = order_func(left_terminal);
                            let right_index = order_func(right_terminal);
                            // Both are terminals, prefer the one that is higher in the order
                            if right_index < left_index {
                                left = right;
                            }
                        }
                        _ => (),
                    }
                }
                Nonterminal(_) | ErrorNonterminal(_) => unreachable!(),
            }
        }
        match left.type_() {
            Terminal(t) | ErrorTerminal(t) => match t {
                TerminalType::Name => Self::Name(Name::new(left)),
                _ => Self::None,
            },
            PyNodeType::ErrorKeyword | PyNodeType::Keyword => Self::Keyword(Keyword::new(left)),
            Nonterminal(_) | ErrorNonterminal(_) => unreachable!("{}", left.type_str()),
        }
    }
}
