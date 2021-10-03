use std::iter::StepBy;

pub use parsa_python::{CodeIndex, NodeIndex};
use parsa_python::{
    NonterminalType::*,
    PyNode, PyNodeType,
    PyNodeType::{ErrorNonterminal, ErrorTerminal, Nonterminal, Terminal},
    PyTree, SiblingIterator, TerminalType,
};

pub trait HasIndex<'db> {
    fn index(&self) -> NodeIndex;

    fn short_debug(&self) -> &'db str;
}

macro_rules! create_struct {
    ($name:ident: $type:expr) => {
        #[derive(Debug, Clone, Copy)]
        pub struct $name<'db>(pub PyNode<'db>);

        impl<'db> $name<'db> {
            #[inline]
            pub fn new(node: PyNode<'db>) -> Self {
                debug_assert_eq!(node.get_type(), $type);
                Self(node)
            }

            #[inline]
            pub fn by_index(tree: &'db PyTree, index: NodeIndex) -> Self {
                Self::new(tree.get_node_by_index(index))
            }
        }

        impl<'db> HasIndex<'db> for $name<'db> {
            #[inline]
            fn index(&self) -> NodeIndex {
                self.0.index
            }

            fn short_debug(&self) -> &'db str {
                self.0
                    .get_code()
                    .get(..20)
                    .unwrap_or_else(|| self.0.get_code())
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
    Stmt: stmt
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
    ImportFromAsName: import_from_as_name

    Primary: primary

    PrimaryTarget: t_primary
    StarTarget: star_target

    Arguments: arguments

    NameDefinition: name_definition
    Atom: atom
    StringsOrBytes: strings

    List: atom
    Set: atom
    Tuple: atom
    Dict: atom
    Comprehension: comprehension
    DictComprehension: dict_comprehension
    Slices: slices
    Slice: slice

    ClassDef: class_def

    FunctionDef: function_def
    ReturnAnnotation: return_annotation
    ReturnStmt: return_stmt
    YieldExpr: yield_expr
    Lambda: lambda
);

create_struct!(Name: Terminal(TerminalType::Name));
create_struct!(Int: Terminal(TerminalType::Number));
create_struct!(Float: Terminal(TerminalType::Number));
create_struct!(Complex: Terminal(TerminalType::Number));
create_struct!(Keyword: PyNodeType::Keyword);

impl<'db> Name<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.0.get_code()
    }

    pub fn start(&self) -> CodeIndex {
        self.0.start()
    }

    pub fn end(&self) -> CodeIndex {
        self.0.end()
    }

    pub fn is_reference(&self) -> bool {
        !self
            .0
            .get_parent()
            .unwrap()
            .is_type(Nonterminal(name_definition))
    }

    pub fn name_definition(&self) -> Option<NameDefinition<'db>> {
        let parent = self.0.get_parent().unwrap();
        if parent.is_type(Nonterminal(name_definition)) {
            Some(NameDefinition::new(parent))
        } else {
            None
        }
    }

    pub fn maybe_primary_parent(&self) -> Option<Primary<'db>> {
        let parent = self.0.get_parent().unwrap();
        if parent.is_type(Nonterminal(primary)) {
            Some(Primary::new(parent))
        } else {
            None
        }
    }

    pub fn expect_function_def(&self) -> FunctionDef<'db> {
        FunctionDef(self.0.get_parent().unwrap().get_parent().unwrap())
    }

    pub fn expect_stmt_like_ancestor(&self) -> StmtLike<'db> {
        let stmt_node = self
            .0
            .get_parent_until(&[
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

impl<'db> Keyword<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.0.get_code()
    }

    pub fn maybe_primary_parent(&self) -> Option<Primary<'db>> {
        let parent = self.0.get_parent().unwrap();
        if parent.is_type(Nonterminal(primary)) {
            Some(Primary(parent))
        } else {
            None
        }
    }
}

impl<'db> List<'db> {
    pub fn unpack(&self) -> ListContent<'db> {
        let n = self.0.get_nth_child(1);
        if n.is_type(Nonterminal(star_named_expressions)) {
            ListContent::Elements(ListElementIterator(n.iter_children().step_by(2)))
        } else if n.is_type(Nonterminal(comprehension)) {
            ListContent::Comprehension(Comprehension(n))
        } else {
            ListContent::None
        }
    }
}

pub enum ListContent<'db> {
    None,
    Elements(ListElementIterator<'db>),
    Comprehension(Comprehension<'db>),
}

pub struct ListElementIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for ListElementIterator<'db> {
    type Item = ListElement<'db>;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|next| {
            if next.is_type(Nonterminal(named_expression)) {
                ListElement::NamedExpression(NamedExpression(next))
            } else {
                ListElement::StarNamedExpression(StarNamedExpression(next))
            }
        })
    }
}

pub enum ListElement<'db> {
    NamedExpression(NamedExpression<'db>),
    StarNamedExpression(StarNamedExpression<'db>),
}

impl<'db> Expression<'db> {
    pub fn unpack(self) -> ExpressionContent<'db> {
        let mut iter = self.0.iter_children();
        let first = iter.next().unwrap();
        if first.is_type(Nonterminal(lambda)) {
            ExpressionContent::Lambda(Lambda::new(first))
        } else if iter.next().is_none() {
            ExpressionContent::Expression(first)
        } else {
            ExpressionContent::Ternary(Ternary::new(self.0))
        }
    }
}

pub enum ExpressionContent<'db> {
    Expression(PyNode<'db>),
    Ternary(Ternary<'db>),
    Lambda(Lambda<'db>),
}

impl<'db> NamedExpression<'db> {
    pub fn unpack(self) -> NamedExpressionContent<'db> {
        let node = self.0.get_nth_child(0);
        if node.is_type(Nonterminal(expression)) {
            NamedExpressionContent::Expression(Expression(node))
        } else {
            let expr = node.get_nth_child(2);
            NamedExpressionContent::Definition(NameDefinition(node), Expression(expr))
        }
    }
}

pub enum NamedExpressionContent<'db> {
    Expression(Expression<'db>),
    Definition(NameDefinition<'db>, Expression<'db>),
}

impl<'db> Stmt<'db> {
    pub fn as_simple_stmts(&self) -> Option<SimpleStmts<'db>> {
        let child = self.0.get_nth_child(0);
        if child.is_type(Nonterminal(simple_stmts)) {
            Some(SimpleStmts::new(child))
        } else {
            None
        }
    }
}

impl<'db> SimpleStmts<'db> {
    pub fn iter(&self) -> SimpleStmtIterator<'db> {
        SimpleStmtIterator(self.0.iter_children().step_by(2))
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
        let simple_child = self.0.get_nth_child(0);
        if simple_child.is_type(Nonterminal(assignment)) {
            SimpleStmtContent::Assignment(Assignment::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_from)) {
            SimpleStmtContent::ImportFrom(ImportFrom::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_name)) {
            SimpleStmtContent::ImportName(ImportName::new(simple_child))
        } else {
            SimpleStmtContent::Other
        }
    }
}

pub enum SimpleStmtContent<'db> {
    Assignment(Assignment<'db>),
    ImportFrom(ImportFrom<'db>),
    ImportName(ImportName<'db>),
    Other,
}

impl<'db> StarExpressions<'db> {
    pub fn unpack(&self) -> StarExpressionContent<'db> {
        let mut iter = self.0.iter_children();
        let expr = iter.next().unwrap();
        if iter.next().is_none() {
            if expr.is_type(Nonterminal(expression)) {
                StarExpressionContent::Expression(Expression(expr))
            } else {
                StarExpressionContent::StarExpression(StarExpression(expr))
            }
        } else {
            StarExpressionContent::Tuple(StarExpressionsTuple(self.0))
        }
    }
}

pub enum StarExpressionContent<'db> {
    Expression(Expression<'db>),
    StarExpression(StarExpression<'db>),
    Tuple(StarExpressionsTuple<'db>),
}

impl<'db> ClassDef<'db> {
    pub fn name(&self) -> Name<'db> {
        Name(self.0.get_nth_child(1))
    }
}

impl<'db> FunctionDef<'db> {
    pub fn from_param_name_index(tree: &'db PyTree, param_name_index: NodeIndex) -> Self {
        Self(
            tree.get_node_by_index(param_name_index)
                .get_parent_until(&[Nonterminal(function_def)])
                .unwrap(),
        )
    }

    pub fn annotation(&self) -> Option<ReturnAnnotation<'db>> {
        let ret = self.0.get_nth_child(3);
        if ret.is_type(Nonterminal(return_annotation)) {
            Some(ReturnAnnotation(ret))
        } else {
            None
        }
    }

    pub fn iter_params(&self) -> ParamIterator<'db> {
        // function_def: "def" name_definition function_def_parameters ...
        // function_def_parameters: "(" [parameters] ")"
        let params = self.0.get_nth_child(2).get_nth_child(1);
        if params.is_type(Nonterminal(parameters)) {
            let positional_only = params
                .iter_children()
                .any(|n| n.is_leaf() && n.get_code() == "/");
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
                        return Some(Self::Item::new(
                            &mut node.iter_children().skip(1),
                            MultiArgs,
                        ));
                    } else if node.is_type(Nonterminal(double_starred_param)) {
                        return Some(Self::Item::new(
                            &mut node.iter_children().skip(1),
                            MultiKwargs,
                        ));
                    }
                }
                None
            }
            Self::Finished => None,
        }
    }
}

pub struct Param<'db> {
    typ: ParamType,
    name_node: PyNode<'db>,
    annotation_node: Option<PyNode<'db>>,
    default_node: Option<PyNode<'db>>,
}

impl<'db> Param<'db> {
    fn new(param_children: &mut impl Iterator<Item = PyNode<'db>>, typ: ParamType) -> Self {
        let name_node = param_children.next().unwrap();
        debug_assert_eq!(name_node.get_type(), Nonterminal(name_definition));
        let annotation_node = param_children
            .next()
            .map(|n: PyNode<'db>| n.get_nth_child(1));
        param_children.next();
        let default_node = param_children.next();
        Self {
            typ,
            name_node: name_node.get_nth_child(0),
            annotation_node,
            default_node,
        }
    }

    pub fn name(&self) -> Name<'db> {
        Name(self.name_node)
    }

    pub fn annotation(&self) -> Option<Expression<'db>> {
        self.annotation_node.map(Expression::new)
    }
}

pub enum ParamType {
    PositionalOnly,
    PositionalOrKeyword,
    MultiArgs,
    MultiKwargs,
    KeywordOnly,
}

impl<'db> ReturnAnnotation<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression(self.0.get_nth_child(1))
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
        // | single_target ":" expression ["=" (yield_expr | star_expressions)]
        // | single_target augassign (yield_expr | star_expressions)
        let mut iterator = self.0.iter_children().skip(1);
        while let Some(child) = iterator.next() {
            if child.is_type(Nonterminal(yield_expr))
                || child.is_type(Nonterminal(star_expressions))
            {
                let iter = AssignmentTargetIterator(self.0.iter_children().step_by(2));
                return AssignmentContent::Normal(iter, Self::right_side(child));
            } else if child.is_type(Nonterminal(expression)) {
                iterator.next();
                let right = iterator.next().map(Self::right_side);
                return AssignmentContent::WithAnnotation(
                    Target::new(self.0),
                    Expression::new(child),
                    right,
                );
            } else if child.is_type(Nonterminal(augassign)) {
                iterator.next();
                let right = Self::right_side(iterator.next().unwrap());
                return AssignmentContent::AugAssign(
                    Target::new(self.0),
                    AugAssign::new(child),
                    right,
                );
            }
        }
        unreachable!()
    }

    fn right_side(child: PyNode) -> AssignmentRightSide {
        if child.is_type(Nonterminal(star_expressions)) {
            return AssignmentRightSide::StarExpressions(StarExpressions(child));
        } else {
            return AssignmentRightSide::YieldExpr(YieldExpr(child));
        }
    }
}

pub enum AssignmentContent<'db> {
    Normal(AssignmentTargetIterator<'db>, AssignmentRightSide<'db>),
    WithAnnotation(
        Target<'db>,
        Expression<'db>,
        Option<AssignmentRightSide<'db>>,
    ),
    AugAssign(Target<'db>, AugAssign<'db>, AssignmentRightSide<'db>),
}

pub enum AssignmentRightSide<'db> {
    YieldExpr(YieldExpr<'db>),
    StarExpressions(StarExpressions<'db>),
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
        for node in self.0.iter_children().skip(1) {
            if node.is_type(Nonterminal(dotted_name)) {
                return (level, Some(DottedName(node)));
            } else if node.get_code() == "." {
                level += 1;
            } else if node.get_code() == "..." {
                level += 3;
            } else if node.get_code() == "import" {
                break;
            }
        }
        (level, None)
    }

    pub fn unpack_targets(&self) -> ImportFromTargets<'db> {
        // import_from_targets:
        //     "*" | "(" ",".import_from_as_name+ ","? ")" | ",".import_from_as_name+
        for node in self.0.iter_children().skip(3) {
            if node.is_type(Nonterminal(import_from_targets)) {
                let first = node.get_nth_child(0);
                if first.is_leaf() && first.get_code() == "*" {
                    return ImportFromTargets::Star;
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
    Star,
    Iterator(ImportFromTargetsIterator<'db>),
}

pub struct ImportFromTargetsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ImportFromTargetsIterator<'db> {
    type Item = ImportFromAsName<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for child in &mut self.0 {
            if child.is_type(Nonterminal(import_from_as_name)) {
                // import_from_as_name: Name "as" name_definition | name_definition
                return Some(ImportFromAsName(child));
            }
        }
        None
    }
}

impl<'db> ImportFromAsName<'db> {
    pub fn name_definition(&self) -> NameDefinition {
        let first = self.0.get_nth_child(0);
        if first.is_type(Nonterminal(name_definition)) {
            NameDefinition(first)
        } else {
            NameDefinition(self.0.get_nth_child(2))
        }
    }

    pub fn import_name(&self) -> Name {
        let first = self.0.get_nth_child(0);
        if first.is_type(Nonterminal(name_definition)) {
            Name::new(first.get_nth_child(0))
        } else {
            Name::new(first)
        }
    }
}
impl<'db> DottedName<'db> {
    pub fn unpack(&self) -> DottedNameContent<'db> {
        let mut children = self.0.iter_children();
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

impl<'db> Primary<'db> {
    pub fn first(&self) -> PrimaryOrAtom<'db> {
        let first = self.0.get_nth_child(0);
        if first.is_type(Nonterminal(atom)) {
            PrimaryOrAtom::Atom(Atom(first))
        } else {
            debug_assert_eq!(first.get_type(), Nonterminal(primary));
            PrimaryOrAtom::Primary(Primary(first))
        }
    }

    pub fn second(self) -> PrimaryContent<'db> {
        let second = self.0.get_nth_child(2);
        if second.is_type(Terminal(TerminalType::Name)) {
            PrimaryContent::Attribute(Name(second))
        } else if second.is_type(Nonterminal(arguments)) {
            PrimaryContent::Execution(ArgumentsDetails::Node(Arguments(second)))
        } else if second.is_type(Nonterminal(named_expression)) {
            PrimaryContent::GetItem(SliceType::NamedExpression(NamedExpression(second)))
        } else if second.is_type(Nonterminal(comprehension)) {
            PrimaryContent::Execution(ArgumentsDetails::Comprehension(Comprehension(second)))
        } else if second.is_type(Nonterminal(slice)) {
            PrimaryContent::GetItem(SliceType::Slice(Slice(second)))
        } else if second.is_type(Nonterminal(slices)) {
            PrimaryContent::GetItem(SliceType::Slices(Slices(second)))
        } else {
            debug_assert_eq!(second.get_code(), ")");
            PrimaryContent::Execution(ArgumentsDetails::None)
        }
    }
}

pub enum PrimaryOrAtom<'db> {
    Primary(Primary<'db>),
    Atom(Atom<'db>),
}

pub enum PrimaryContent<'db> {
    Attribute(Name<'db>),
    Execution(ArgumentsDetails<'db>),
    GetItem(SliceType<'db>),
}

#[derive(Clone, Copy)]
pub enum SliceType<'db> {
    Slices(Slices<'db>),
    Slice(Slice<'db>),
    NamedExpression(NamedExpression<'db>),
}

impl<'db> Arguments<'db> {
    pub fn iter(&self) -> ArgumentsIterator<'db> {
        ArgumentsIterator(self.0.iter_children())
    }
}

pub struct ArgumentsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ArgumentsIterator<'db> {
    type Item = Argument<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for node in &mut self.0 {
            if node.is_type(Nonterminal(named_expression)) {
                return Some(Argument::Positional(NamedExpression(node)));
            } else if node.is_type(Nonterminal(kwargs)) {
                *self = Self(node.iter_children());
                return self.next();
            } else if node.is_type(Nonterminal(kwarg)) {
                // kwarg: Name "=" expression
                let mut kwarg_iterator = node.iter_children();
                let name = kwarg_iterator.next().unwrap().get_code();
                kwarg_iterator.next();
                let arg = kwarg_iterator.next().unwrap();
                return Some(Argument::Keyword(name, Expression(arg)));
            } else if node.is_type(Nonterminal(starred_expression)) {
                return Some(Argument::Starred(Expression(node.get_nth_child(1))));
            } else if node.is_type(Nonterminal(double_starred_expression)) {
                return Some(Argument::DoubleStarred(Expression(node.get_nth_child(1))));
            }
        }
        None
    }
}

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
    pub fn by_index(tree: &'db PyTree, index: NodeIndex) -> Self {
        let node = tree.get_node_by_index(index);
        if node.is_type(Nonterminal(return_stmt)) {
            ReturnOrYield::Return(ReturnStmt(node))
        } else {
            ReturnOrYield::Yield(YieldExpr(node))
        }
    }
}

impl<'db> ReturnStmt<'db> {
    pub fn star_expressions(&self) -> StarExpressions<'db> {
        StarExpressions(self.0.get_nth_child(1))
    }
}

impl<'db> NameDefinition<'db> {
    #[inline]
    pub fn name(&self) -> Name<'db> {
        Name(self.0.get_nth_child(0))
    }
}

impl<'db> Atom<'db> {
    #[inline]
    pub fn unpack(&self) -> AtomContent<'db> {
        let mut iter = self.0.iter_children();
        let first = iter.next().unwrap();

        match first.get_type() {
            Terminal(TerminalType::Name) => AtomContent::Name(Name(first)),
            Terminal(TerminalType::Number) => {
                let code = first.get_code();
                if code.contains('j') {
                    AtomContent::Complex(Complex(first))
                } else if code.contains('.') {
                    AtomContent::Float(Float(first))
                } else {
                    AtomContent::Int(Int(first))
                }
            }
            Nonterminal(strings) => AtomContent::StringsOrBytes(StringsOrBytes(first)),
            PyNodeType::Keyword => match first.get_code() {
                "None" => AtomContent::None,
                "True" | "False" => AtomContent::Boolean(Keyword(first)),
                "..." => AtomContent::Ellipsis,
                "(" => {
                    let next_node = iter.next().unwrap();
                    match next_node.get_type() {
                        Nonterminal(tuple_content) => AtomContent::Tuple(Tuple(self.0)),
                        Nonterminal(yield_expr) => AtomContent::YieldExpr(YieldExpr(next_node)),
                        Nonterminal(named_expression) => {
                            AtomContent::NamedExpression(NamedExpression(next_node))
                        }
                        Nonterminal(comprehension) => {
                            AtomContent::GeneratorComprehension(Comprehension(next_node))
                        }
                        PyNodeType::Keyword => {
                            debug_assert_eq!(next_node.get_code(), ")");
                            AtomContent::Tuple(Tuple(self.0))
                        }
                        _ => unreachable!(),
                    }
                }
                "[" => {
                    let next_node = iter.next().unwrap();
                    if next_node.is_type(Nonterminal(comprehension)) {
                        AtomContent::ListComprehension(Comprehension(next_node))
                    } else {
                        AtomContent::List(List(self.0))
                    }
                }
                "{" => {
                    let next_node = iter.next().unwrap();
                    match next_node.get_type() {
                        Nonterminal(dict_content) => AtomContent::Dict(Dict(self.0)),
                        Nonterminal(dict_comprehension) => {
                            AtomContent::DictComprehension(DictComprehension(next_node))
                        }
                        Nonterminal(star_named_expression) => AtomContent::Set(Set(self.0)),
                        Nonterminal(comprehension) => {
                            AtomContent::SetComprehension(Comprehension(next_node))
                        }
                        PyNodeType::Keyword => {
                            debug_assert_eq!(next_node.get_code(), "}");
                            AtomContent::Dict(Dict(self.0))
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

    None,
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

impl<'db> StringsOrBytes<'db> {
    pub fn starts_with_string(&self) -> bool {
        let code = self.0.get_nth_child(0).get_code();
        for byte in code.bytes() {
            if byte == b'"' || byte == b'\'' {
                break;
            } else if byte == b'b' || byte == b'B' {
                return false;
            }
        }
        true
    }
}

pub enum NameOrKeywordLookup<'db> {
    Name(Name<'db>),
    Keyword(Keyword<'db>),
    None,
}

pub enum Target<'db> {
    Tuple(TargetIterator<'db>),
    Name(Name<'db>),
    NameExpression(PrimaryTarget<'db>, Name<'db>),
    IndexExpression(PrimaryTarget<'db>),
    Starred(StarTarget<'db>),
}

impl<'db> Target<'db> {
    fn new(node: PyNode<'db>) -> Self {
        if node.is_type(Nonterminal(single_target)) {
            todo!()
        }
        // star_targets: ",".star_target+ [","]
        // star_target:? "*"? (t_primary | star_target_brackets | name_definition)
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            if first.is_type(Nonterminal(name_definition)) {
                Self::Name(Name::new(first.get_nth_child(0)))
            } else if first.is_type(Nonterminal(t_primary)) {
                first
                    .iter_children()
                    .find(|x| x.is_type(Nonterminal(name_definition)))
                    .map(|name_def| {
                        Self::NameExpression(
                            PrimaryTarget::new(first),
                            Name::new(name_def.get_nth_child(0)),
                        )
                    })
                    .unwrap_or_else(|| Self::IndexExpression(PrimaryTarget(first)))
            } else if first.is_type(Nonterminal(star_target_brackets)) {
                todo!("star_target_brackets")
            } else if first.is_type(Nonterminal(star_target)) {
                Self::Starred(StarTarget::new(first.get_nth_child(1)))
            } else {
                unreachable!();
            }
        } else {
            Self::Tuple(TargetIterator {
                siblings: node.iter_children(),
            })
        }
    }
}

pub struct TargetIterator<'db> {
    siblings: SiblingIterator<'db>,
}

impl<'db> Iterator for TargetIterator<'db> {
    type Item = Target<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.siblings.next();
        if let Some(sibling) = current {
            self.siblings.next();
            Some(Target::new(sibling))
        } else {
            None
        }
    }
}

impl<'db> NameOrKeywordLookup<'db> {
    pub fn from_position(tree: &'db PyTree, position: CodeIndex) -> Self {
        // First check the token left and right of the cursor
        let mut left = tree.get_leaf_by_position(position);
        let mut right = left;
        if left.start() == position {
            if let Some(n) = left.get_previous_leaf() {
                if n.end() == position {
                    left = n;
                }
            }
        } else if left.end() == position {
            if let Some(n) = left.get_next_leaf() {
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
            match left.get_type() {
                PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                    match right.get_type() {
                        PyNodeType::ErrorKeyword | PyNodeType::Keyword => {
                            let is_alpha =
                                |n: PyNode| n.get_code().chars().all(|x| x.is_alphanumeric());
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
                    match right.get_type() {
                        Terminal(right_terminal) | ErrorTerminal(right_terminal) => {
                            let order_func =
                                |typ| order.iter().position(|&t| t == typ).unwrap_or(usize::MAX);
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
        match left.get_type() {
            Terminal(t) | ErrorTerminal(t) => match t {
                TerminalType::Name => Self::Name(Name(left)),
                _ => Self::None,
            },
            PyNodeType::ErrorKeyword | PyNodeType::Keyword => Self::Keyword(Keyword(left)),
            Nonterminal(_) | ErrorNonterminal(_) => unreachable!("{}", left.type_str()),
        }
    }
}
