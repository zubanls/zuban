use std::iter::StepBy;

pub use parsa_python::{CodeIndex, NodeIndex};
use parsa_python::{
    NonterminalType::*,
    PyNode, PyNodeType,
    PyNodeType::{Nonterminal, Terminal},
    PyTree, SiblingIterator, TerminalType,
};

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

            #[inline]
            pub fn index(&self) -> NodeIndex {
                self.0.index
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
    NamedExpression: named_expression

    Primary: primary

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
    Annotation: annotation
    ReturnStmt: return_stmt
    YieldExpr: yield_expr
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
            Some(NameDefinition(parent))
        } else {
            None
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

impl<'db> Stmt<'db> {}

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

    pub fn annotation(&self) -> Option<Annotation<'db>> {
        self.annotation_node.map(Annotation)
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

impl<'db> Annotation<'db> {
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
    pub fn unpack(&self) -> AtomContent {
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
