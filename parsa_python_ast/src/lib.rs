use parsa_python::{
    NodeIndex,
    NonterminalType::*,
    PyNode,
    PyNodeType::{Nonterminal, Terminal},
    PyTree, SiblingIterator, TerminalType,
};

macro_rules! create_struct {
    ($name:ident: $type:expr) => {
        #[derive(Debug)]
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
    Expression: expression

    ClassDef: class_def

    FunctionDef: function_def
    ReturnAnnotation: return_annotation
    Annotation: annotation

);

create_struct!(Name: Terminal(TerminalType::Name));

impl<'db> Name<'db> {
    pub fn as_str(&self) -> &'db str {
        self.0.get_code()
    }
}

impl<'db> Stmt<'db> {}

impl<'db> StarExpressions<'db> {
    pub fn unpack(&self) -> StarExpressionContent<'db> {
        let mut iter = self.0.iter_children();
        let expr = iter.next().unwrap();
        if iter.next().is_none() {
            if expr.is_type(Nonterminal(expression)) {
                StarExpressionContent::Expression(expr)
            } else {
                StarExpressionContent::StarExpression(StarExpression(expr))
            }
        } else {
            StarExpressionContent::Tuple(StarExpressionsTuple(self.0))
        }
    }
}

pub enum StarExpressionContent<'db> {
    Expression(PyNode<'db>),
    StarExpression(StarExpression<'db>),
    Tuple(StarExpressionsTuple<'db>),
}

impl<'db> ClassDef<'db> {
    pub fn name(&self) -> Name<'db> {
        Name(self.0.get_nth_child(1))
    }
}

impl<'db> FunctionDef<'db> {
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
