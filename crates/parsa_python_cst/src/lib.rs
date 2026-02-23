mod bytes;
mod code_actions;
mod completion;
mod match_stmt;
mod ranges;
mod signatures;
mod strings;

use std::{
    borrow::Cow,
    iter::{Skip, StepBy},
    str::from_utf8,
};

pub use bytes::parse_python_bytes_literal;
use completion::scope_for_node;
pub use completion::{CompletionContext, CompletionNode, RestNode, Scope};
pub use match_stmt::{
    CasePattern, KeyEntryInPattern, LiteralPatternContent, MappingPatternItem, ParamPattern,
    PatternKind, SequencePatternItem, StarPatternContent, SubjectExprContent,
};
pub use parsa_python::{CodeIndex, NodeIndex, is_identifier, keywords_contain};
use parsa_python::{
    NonterminalType::*,
    PyNode,
    PyNodeType::{self, ErrorNonterminal, ErrorTerminal, Nonterminal, Terminal},
    PyTree, SearchIterator, SiblingIterator, TerminalType, parse,
};
pub use ranges::Range;
pub use signatures::{SignatureArg, SignatureArgsIterator, SignatureBase};
pub use strings::PythonString;

pub const NAME_DEF_TO_NAME_DIFFERENCE: u32 = 1;

#[derive(Clone)]
pub struct Tree(PyTree);

impl Tree {
    pub fn parse(code: Box<str>) -> Self {
        Self(parse(code))
    }

    pub fn invalid_empty() -> Self {
        Self(PyTree::empty())
    }

    pub fn length(&self) -> usize {
        self.0.length()
    }

    pub fn code(&self) -> &str {
        self.0.as_code()
    }

    pub fn root(&self) -> File<'_> {
        File::new(self.0.root_node())
    }

    pub fn maybe_star_expressions(&self) -> Option<StarExpressions<'_>> {
        let mut node = self.0.root_node();
        for (nonterminal, expected_node_count) in [
            (stmt, 2),
            (simple_stmts, 1),
            (simple_stmt, 2),
            (star_expressions, 1),
        ] {
            if node.iter_children().count() != expected_node_count {
                return None;
            }
            node = node.nth_child(0);
            if !node.is_type(Nonterminal(nonterminal)) {
                return None;
            }
        }
        Some(StarExpressions::new(node))
    }

    pub fn node_parent_scope(&self, index: NodeIndex) -> Scope<'_> {
        scope_for_node(self.0.node_by_index(index))
    }

    pub fn node_start_position(&self, index: NodeIndex) -> CodeIndex {
        self.0.node_by_index(index).start()
    }

    pub fn node_end_position(&self, index: NodeIndex) -> CodeIndex {
        self.0.node_by_index(index).end()
    }

    pub fn node_end_position_without_whitespace(&self, index: NodeIndex) -> CodeIndex {
        let node = self.0.node_by_index(index);
        let mut leaf = node.last_leaf_in_subtree();
        while leaf.is_type(Terminal(TerminalType::Newline))
            || leaf.is_type(Terminal(TerminalType::Dedent))
        {
            leaf = leaf.previous_leaf().unwrap();
        }
        leaf.end()
    }

    pub fn type_ignore_comment_for(
        &self,
        start: CodeIndex,
        end: CodeIndex,
    ) -> Option<TypeIgnoreComment<'_>> {
        // Returns Some(None) when there is a type: ignore
        // Returns Some("foo") when there is a type: ignore['foo']
        let code = self.code();
        let relevant_region = if let Some(newline) = code[end as usize..].find(['\n', '\r']) {
            &code[start as usize..end as usize + newline]
        } else {
            &code[start as usize..]
        };
        Self::type_ignore_comment_for_region(start, relevant_region)
    }

    fn type_ignore_comment_for_region(
        mut start_at: CodeIndex,
        region: &str,
    ) -> Option<TypeIgnoreComment<'_>> {
        for line in region.split(['\n', '\r']) {
            let mut iterator = line.split('#');
            start_at += iterator.next().unwrap().len() as CodeIndex + 1;
            for comment in iterator {
                let rest = comment.trim_start_matches(' ');
                let mut kind = "type";
                if let Some(ignore) = rest.strip_prefix("type:").or_else(|| {
                    kind = "zuban";
                    rest.strip_prefix("zuban:")
                }) {
                    let ignore = ignore.trim_start_matches(' ');
                    let r = maybe_type_ignore(
                        kind,
                        start_at + (comment.len() - ignore.len()) as CodeIndex,
                        ignore,
                    );
                    if r.is_some() {
                        return r;
                    }
                } else {
                    break;
                }
                start_at += comment.len() as CodeIndex + 1;
            }
            start_at += 1;
        }
        None
    }

    pub fn has_type_ignore_at_start(&self) -> Result<bool, &str> {
        match Self::type_ignore_comment_for_region(0, self.before_first_statement()) {
            Some(TypeIgnoreComment::WithCodes { codes: code, .. }) => Err(code),
            Some(TypeIgnoreComment::WithoutCode) => Ok(true),
            None => Ok(false),
        }
    }

    fn before_first_statement(&self) -> &str {
        let start = self.0.root_node().nth_child(0).start();
        &self.code()[0..start as usize]
    }

    pub fn mypy_inline_config_directives(&self) -> impl Iterator<Item = (CodeIndex, &str)> {
        const PREFIX: &str = "# mypy: ";
        let mut code_index_start = 0;
        self.code().split('\n').filter_map(move |line| {
            let result = line
                .strip_prefix(PREFIX)
                .map(|rest| (code_index_start + PREFIX.len() as CodeIndex, rest));
            code_index_start += line.len() as CodeIndex + 1;
            result
        })
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

    pub fn goto_node(&self, position: CodeIndex) -> (Scope<'_>, GotoNode<'_>) {
        // First check the token left and right of the cursor
        let mut left = self.0.leaf_by_position(position);
        let mut right = left;
        if left.start() == position {
            if let Some(n) = left.previous_leaf()
                && n.end() == position
            {
                left = n;
            }
        } else if left.end() == position
            && let Some(n) = left.next_leaf()
            && n.start() == position
        {
            right = n;
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
        let goto_node = match left.type_() {
            Terminal(t) | ErrorTerminal(t) => match t {
                TerminalType::Name => {
                    let parent = left.parent().unwrap();
                    if parent.is_type(Nonterminal(primary)) {
                        GotoNode::Primary(Primary::new(parent))
                    } else if parent.is_type(Nonterminal(import_from_as_name)) {
                        GotoNode::ImportFromAsName {
                            import_as_name: ImportFromAsName::new(parent),
                            on_name: Name::new(left),
                        }
                    } else if parent.is_type(Nonterminal(name_def)) {
                        let par_parent = parent.parent().unwrap();
                        if par_parent.is_type(Nonterminal(import_from_as_name)) {
                            GotoNode::ImportFromAsName {
                                import_as_name: ImportFromAsName::new(par_parent),
                                on_name: Name::new(left),
                            }
                        } else if par_parent.is_type(Nonterminal(t_primary)) {
                            GotoNode::PrimaryTarget(PrimaryTarget::new(par_parent))
                        } else if par_parent.is_type(Nonterminal(global_stmt)) {
                            GotoNode::GlobalName(NameDef::new(parent))
                        } else if par_parent.is_type(Nonterminal(nonlocal_stmt)) {
                            GotoNode::NonlocalName(NameDef::new(parent))
                        } else {
                            GotoNode::Name(Name::new(left))
                        }
                    } else if parent.is_type(Nonterminal(t_primary)) {
                        GotoNode::PrimaryTarget(PrimaryTarget::new(parent))
                    } else {
                        GotoNode::Name(Name::new(left))
                    }
                }
                _ => GotoNode::None,
            },
            PyNodeType::Keyword => {
                let parent = left.parent().unwrap();
                if parent.is_type(Nonterminal(primary)) {
                    GotoNode::Primary(Primary::new(parent))
                } else if parent.is_type(Nonterminal(t_primary)) {
                    GotoNode::PrimaryTarget(PrimaryTarget::new(parent))
                } else if parent.is_type(Nonterminal(atom)) {
                    GotoNode::Atom(Atom::new(parent))
                } else {
                    (|| {
                        let previous = if parent.is_type(Nonterminal(comp_op))
                            || parent.is_type(Nonterminal(augassign))
                        {
                            left.parent().unwrap().previous_sibling()
                        } else {
                            left.previous_sibling()
                        };
                        let inplace = |inplace_magic_method, normal_magic_method| {
                            if let Some(previous) = previous
                                && previous.is_type(Nonterminal(single_target))
                            {
                                GotoNode::AugAssignOperator {
                                    operator: Keyword::new(left),
                                    target: Target::new_single_target(previous),
                                    inplace_magic_method,
                                    normal_magic_method,
                                }
                            } else {
                                GotoNode::None
                            }
                        };
                        let magic_method = match left.as_code() {
                            "==" => "__eq__",
                            "!=" => "__ne__",
                            "<" => "__lt__",
                            ">" => "__gt__",
                            "<=" => "__le__",
                            ">=" => "__ge__",

                            "|" => "__or__",
                            "&" => "__and__",
                            "^" => "__xor__",

                            "+" if previous.is_none() => "__pos__",
                            "-" if previous.is_none() => "__neg__",
                            "~" if previous.is_none() => "__invert__",

                            "+" => "__add__",
                            "-" => "__sub__",
                            "*" => "__mul__",
                            "/" => "__truediv__",
                            "//" => "__floordiv__",
                            "%" => "__mod__",
                            ">>" => "__rshift__",
                            "<<" => "__lshift__",
                            "**" => "__pow__",
                            "@" => "__matmul__",

                            "|=" => return inplace("__ior__", "__or__"),
                            "&=" => return inplace("__iand__", "__and__"),
                            "^=" => return inplace("__ixor__", "__xor__"),
                            "+=" => return inplace("__iadd__", "__add__"),
                            "-=" => return inplace("__isub__", "__sub__"),
                            "*=" => return inplace("__imul__", "__mul__"),
                            "/=" => return inplace("__itruediv__", "__truediv__"),
                            "//=" => return inplace("__ifloordiv__", "__floordiv__"),
                            "%=" => return inplace("__imod__", "__mod__"),
                            ">>=" => return inplace("__irshift__", "__rshift__"),
                            "<<=" => return inplace("__ilshift__", "__lshift__"),
                            "**=" => return inplace("__ipow__", "__pow__"),
                            "@=" => return inplace("__imatmul__", "__matmul__"),
                            _ => return GotoNode::None,
                        };
                        if let Some(first) = previous.or_else(|| left.next_sibling())
                            && let Some(first) = ExpressionPart::maybe_new(first)
                        {
                            GotoNode::Operator {
                                first,
                                magic_method,
                                operator: Keyword::new(left),
                            }
                        } else {
                            GotoNode::None
                        }
                    })()
                }
            }
            PyNodeType::ErrorKeyword => GotoNode::None,
            Nonterminal(_) | ErrorNonterminal(_) => unreachable!("{}", left.type_str()),
        };
        (scope_for_node(left), goto_node)
    }

    pub fn filter_all_names<'x>(
        &'x self,
        start_at_code_index: Option<CodeIndex>,
    ) -> impl Iterator<Item = Name<'x>> {
        let start_at_node_index = if let Some(start_at_code_index) = start_at_code_index {
            let mut leaf = self.0.leaf_by_position(start_at_code_index);
            if start_at_code_index == leaf.start() {
                leaf = leaf.previous_leaf().unwrap_or(leaf);
            }
            leaf.index as usize
        } else {
            0
        };
        self.0
            .nodes()
            .skip(start_at_node_index)
            .filter(|&n| n.is_type(Terminal(TerminalType::Name)))
            .map(Name::new)
    }

    pub fn folding_blocks(&self) -> impl Iterator<Item = (CodeIndex, CodeIndex)> {
        self.0.nodes().filter_map(|n| {
            let end = || {
                let mut leaf = n.last_leaf_in_subtree();
                while leaf.is_type(Terminal(TerminalType::Dedent)) {
                    leaf = leaf.previous_leaf().unwrap();
                }
                leaf.start()
            };
            if n.is_type(Nonterminal(match_stmt)) {
                return Some((n.nth_child(3).start(), end()));
            }
            if !n.is_type(Nonterminal(block)) || n.nth_child(0).is_type(Nonterminal(simple_stmts)) {
                return None;
            }
            Some((n.start(), end()))
        })
    }

    pub fn potential_inlay_hints<'x>(
        &'x self,
        start: CodeIndex,
        end: CodeIndex,
    ) -> impl Iterator<Item = PotentialInlayHint<'x>> {
        let leaf = self.0.leaf_by_position(start);
        let skip = if let Some(prev) = leaf.previous_leaf() {
            prev.index
        } else {
            0
        };
        self.0
            .nodes()
            .skip(skip as usize)
            .take_while(move |n| n.start() <= end)
            .filter_map(|n| {
                if n.is_type(Nonterminal(function_def)) {
                    Some(PotentialInlayHint::FunctionDef(FunctionDef::new(n)))
                } else if n.is_type(Nonterminal(assignment)) {
                    Some(PotentialInlayHint::Assignment(Assignment::new(n)))
                } else {
                    None
                }
            })
    }
}

pub enum TypeIgnoreComment<'db> {
    WithCodes {
        codes: &'db str,
        kind: &'static str,
        codes_start_at_index: CodeIndex,
    },
    WithoutCode,
}

pub enum PotentialInlayHint<'db> {
    FunctionDef(FunctionDef<'db>),
    Assignment(Assignment<'db>),
}

pub fn maybe_type_ignore<'db>(
    kind: &'static str,
    start_at: CodeIndex,
    text: &'db str,
) -> Option<TypeIgnoreComment<'db>> {
    if let Some(after) = text.strip_prefix("ignore") {
        let trimmed = after.trim_start_matches(' ');
        let start_at = start_at + (text.len() - trimmed.len()) as CodeIndex;
        let trimmed = trimmed.trim_end_matches(' ');
        if let Some(trimmed) = trimmed.strip_prefix('[')
            && let Some(trimmed) = trimmed.strip_suffix(']')
            && !trimmed.is_empty()
        {
            return Some(TypeIgnoreComment::WithCodes {
                kind,
                codes: trimmed,
                codes_start_at_index: start_at + 1,
            });
        }

        if after.is_empty() || after.starts_with([' ', '\t']) {
            return Some(TypeIgnoreComment::WithoutCode);
        }
    }
    None
}

pub trait InterestingNodeSearcher<'db> {
    fn search_interesting_nodes(&self) -> InterestingNodes<'db>;
}

// A bit special, since this does not make much sense except for zuban's NameBinder.
pub enum InterestingNode<'db> {
    Name(Name<'db>),
    Conjunction(Conjunction<'db>),
    Disjunction(Disjunction<'db>),
    YieldExpr(YieldExpr<'db>),
    Lambda(Lambda<'db>),
    Ternary(Ternary<'db>),
    Comprehension(Comprehension<'db>),
    DictComprehension(DictComprehension<'db>),
    DottedPatternName(DottedPatternName<'db>),
    Walrus(Walrus<'db>),
}
pub struct InterestingNodes<'db>(SearchIterator<'db>);

impl<'db> Iterator for InterestingNodes<'db> {
    type Item = InterestingNode<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| {
            if n.is_type(Terminal(TerminalType::Name)) {
                InterestingNode::Name(Name::new(n))
            } else if n.is_type(Nonterminal(conjunction)) {
                InterestingNode::Conjunction(Conjunction::new(n))
            } else if n.is_type(Nonterminal(disjunction)) {
                InterestingNode::Disjunction(Disjunction::new(n))
            } else if n.is_type(Nonterminal(yield_expr)) {
                InterestingNode::YieldExpr(YieldExpr::new(n))
            } else if n.is_type(Nonterminal(lambda)) {
                InterestingNode::Lambda(Lambda::new(n))
            } else if n.is_type(Nonterminal(ternary)) {
                InterestingNode::Ternary(Ternary::new(n))
            } else if n.is_type(Nonterminal(comprehension)) {
                InterestingNode::Comprehension(Comprehension::new(n))
            } else if n.is_type(Nonterminal(dict_comprehension)) {
                InterestingNode::DictComprehension(DictComprehension::new(n))
            } else if n.is_type(Nonterminal(dotted_pattern_name)) {
                InterestingNode::DottedPatternName(DottedPatternName::new(n))
            } else {
                debug_assert_eq!(n.type_(), Nonterminal(walrus));
                InterestingNode::Walrus(Walrus::new(n))
            }
        })
    }
}

macro_rules! create_interesting_node_searcher {
    ($name:ident) => {
        impl<'db> InterestingNodeSearcher<'db> for $name<'db> {
            fn search_interesting_nodes(&self) -> InterestingNodes<'db> {
                const SEARCH_NAMES: &[PyNodeType] = &[
                    Terminal(TerminalType::Name),
                    Nonterminal(conjunction),
                    Nonterminal(disjunction),
                    Nonterminal(yield_expr),
                    Nonterminal(lambda),
                    Nonterminal(ternary),
                    Nonterminal(comprehension),
                    Nonterminal(dict_comprehension),
                    Nonterminal(dotted_pattern_name),
                    Nonterminal(walrus),
                ];
                InterestingNodes(self.node.search(SEARCH_NAMES, true))
            }
        }
    };
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
            pub fn length(&self) -> CodeIndex {
                self.node.length()
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

        create_interesting_node_searcher!($name);
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
    SimpleStmt: simple_stmt

    ForStmt: for_stmt
    WhileStmt: while_stmt
    WithStmt: with_stmt
    IfStmt: if_stmt
    TryStmt: try_stmt
    ElseBlock: else_block
    ExceptBlock: except_block
    ExceptStarBlock: except_star_block
    ExceptExpression: except_expression
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
    TypeAlias: type_alias

    Expressions: expressions
    StarExpressions: star_expressions
    StarExpressionsTuple: star_expressions
    StarExpression: star_expression
    StarNamedExpression: star_named_expression
    StarredExpression: starred_expression
    StarStarExpression: double_starred_expression
    Expression: expression
    Ternary: ternary
    NamedExpression: named_expression
    Walrus: walrus

    Assignment: assignment
    AugAssign: augassign

    ImportFrom: import_from
    ImportName: import_name
    DottedImportName: dotted_import_name
    DottedAsName: dotted_as_name
    ImportFromAsName: import_from_as_name

    Disjunction: disjunction
    Conjunction: conjunction
    Inversion: inversion
    Comparisons: comparison
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
    DelTargets: del_targets

    Arguments: arguments
    Kwarg: kwarg

    NameDef: name_def
    Atom: atom
    Strings: strings
    Bytes: bytes
    FString: fstring
    FStringExpr: fstring_expr
    FStringFormatSpec: fstring_format_spec
    FStringConversion: fstring_conversion

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
    StarAnnotation: star_annotation
    ReturnStmt: return_stmt
    YieldExpr: yield_expr
    YieldFrom: yield_from
    Lambda: lambda

    StarTargets: star_targets
    WithItems: with_items
    WithItem: with_item

    SubjectExpr: subject_expr
    CaseBlock: case_block
    Guard: guard
    Pattern: pattern
    OpenSequencePattern: open_sequence_pattern
    OrPattern: or_pattern
    LiteralPattern: literal_pattern
    ComplexNumber: complex_number
    SignedNumber: signed_number
    WildcardPattern: wildcard_pattern
    GroupPattern: group_pattern
    SequencePattern: sequence_pattern
    StarPattern: star_pattern
    MappingPattern: mapping_pattern
    KeyValuePattern: key_value_pattern
    DoubleStarPattern: double_star_pattern
    ClassPattern: class_pattern
    KeywordPattern: keyword_pattern
    DottedPatternName: dotted_pattern_name

    TypeParams: type_params
    TypeParam: type_param
    TypeParamBound: type_param_bound
    TypeParamDefault: type_param_default
    TypeParamStarredDefault: type_param_starred_default

    // Error recovery
    BrokenScope: broken_scope
);

create_struct!(Name: Terminal(TerminalType::Name));
create_struct!(Int: Terminal(TerminalType::Number));
create_struct!(Float: Terminal(TerminalType::Number));
create_struct!(Complex: Terminal(TerminalType::Number));
create_struct!(StringLiteral: Terminal(TerminalType::String));
create_struct!(BytesLiteral: Terminal(TerminalType::Bytes));
create_struct!(FStringString: Terminal(TerminalType::FStringString));
create_struct!(Keyword: PyNodeType::Keyword);

impl<'db> Name<'db> {
    #[inline]
    pub fn as_str(&self) -> &'db str {
        self.node.as_code()
    }

    pub fn is_reference(&self) -> bool {
        !self.node.parent().unwrap().is_type(Nonterminal(name_def))
    }

    pub fn name_def(&self) -> Option<NameDef<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(name_def)) {
            Some(NameDef::new(parent))
        } else {
            None
        }
    }

    pub fn name_def_index(&self) -> NodeIndex {
        debug_assert_eq!(
            self.name_def().unwrap().index(),
            self.index() - NAME_DEF_TO_NAME_DIFFERENCE
        );
        self.index() - NAME_DEF_TO_NAME_DIFFERENCE
    }

    pub fn expect_type(&self) -> TypeLike<'db> {
        let Some(n) = self.name_def() else {
            return TypeLike::Other;
        };
        n.expect_type()
    }

    pub fn simple_parent(&self) -> SimpleNameParent<'db> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(atom)) {
            SimpleNameParent::Atom
        } else if parent.is_type(Nonterminal(name_def)) {
            SimpleNameParent::NameDef(NameDef::new(parent))
        } else {
            SimpleNameParent::Other
        }
    }

    pub fn parent(&self) -> NameParent<'db> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(atom)) {
            NameParent::Atom(Atom::new(parent))
        } else if parent.is_type(Nonterminal(name_def)) {
            NameParent::NameDef(NameDef::new(parent))
        } else if parent.is_type(Nonterminal(primary)) {
            NameParent::Primary(Primary::new(parent))
        } else if parent.is_type(Nonterminal(t_primary)) {
            NameParent::PrimaryTarget(PrimaryTarget::new(parent))
        } else if parent.is_type(Nonterminal(kwarg)) {
            NameParent::Kwarg(Kwarg::new(parent))
        } else if parent.is_type(Nonterminal(keyword_pattern)) {
            NameParent::KeywordPattern(KeywordPattern::new(parent))
        } else if parent.is_type(Nonterminal(import_from_as_name)) {
            NameParent::ImportFromAsName(ImportFromAsName::new(parent))
        } else if parent.is_type(Nonterminal(dotted_import_name)) {
            NameParent::DottedImportName(DottedImportName::new(parent))
        } else if parent.is_type(Nonterminal(dotted_pattern_name)) {
            NameParent::DottedPatternName(DottedPatternName::new(parent))
        } else if parent.is_type(ErrorNonterminal(kwarg)) {
            NameParent::Error
        } else {
            assert!(
                parent.is_type(Nonterminal(fstring_conversion)),
                "{parent:?}"
            );
            NameParent::FStringConversion(FStringConversion::new(parent))
        }
    }

    pub fn is_part_of_primary_ancestors(&self) -> bool {
        let parent = self.node.parent().unwrap();
        if !parent.is_type(Nonterminal(atom)) && !parent.is_type(Nonterminal(primary)) {
            return false;
        }
        let parent = parent.parent().unwrap();
        parent.is_type(Nonterminal(primary)) && self.node.index < parent.nth_child(1).index
    }

    pub fn maybe_atom_of_primary(&self) -> Option<Primary<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(atom)) {
            let par_par = parent.parent().unwrap();
            par_par
                .is_type(Nonterminal(primary))
                .then(|| Primary::new(par_par))
        } else {
            None
        }
    }

    pub fn maybe_assignment_definition_name(&self) -> Option<Assignment<'db>> {
        self.name_def()?.maybe_assignment_definition()
    }

    pub fn maybe_self_assignment_name_on_self_like(&self) -> Option<Assignment<'db>> {
        let node = self
            .node
            .parent_until(&[Nonterminal(assignment), Nonterminal(stmt)])
            .expect("There should always be a stmt");
        if node.is_type(Nonterminal(assignment)) {
            Some(Assignment::new(node))
        } else {
            None
        }
    }

    pub fn maybe_annotated(&self) -> Option<Annotation<'db>> {
        let maybe_colon = self.node.next_leaf()?;
        if maybe_colon.as_code() != ":" {
            return None;
        }
        let maybe_annotated = maybe_colon.parent()?;
        maybe_annotated
            .is_type(Nonterminal(annotation))
            .then(|| Annotation::new(maybe_annotated))
    }

    pub fn is_assignment_annotation_without_definition(&self) -> bool {
        let node = self
            .node
            .parent_until(&[Nonterminal(single_target), Nonterminal(stmt)])
            .expect("There should always be a stmt");
        node.is_type(Nonterminal(single_target)) && {
            debug_assert_eq!(node.parent().unwrap().type_(), Nonterminal(assignment));
            let annotation_node = node.next_sibling().unwrap();
            debug_assert_eq!(annotation_node.type_(), Nonterminal(annotation));
            annotation_node.next_sibling().is_none()
        }
    }

    pub fn expect_as_param_of_function(&self) -> FunctionDef<'db> {
        let params = self
            .node
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        debug_assert_eq!(params.type_(), Nonterminal(parameters));
        let func_node = params.parent().unwrap().parent().unwrap();
        FunctionDef::new(func_node)
    }

    pub fn is_name_of_func(&self) -> bool {
        let Some(n) = self.name_def() else {
            return false;
        };
        n.node.parent().unwrap().is_type(Nonterminal(function_def))
    }

    pub fn parent_scope(&self) -> Scope<'db> {
        scope_for_node(self.node)
    }

    pub fn clean_docstring(&self) -> Cow<'db, str> {
        let docstr = |n: &Self| {
            let name_def_ = n.name_def()?;
            let strings_ = if let Some(func) = name_def_.maybe_name_of_func() {
                func.docstring()
            } else {
                name_def_.maybe_name_of_class()?.docstring()
            };
            strings_?.clean_docstring()
        };
        docstr(self).unwrap_or(Cow::Borrowed(""))
    }
}

#[derive(Debug)]
pub enum SimpleNameParent<'db> {
    NameDef(NameDef<'db>),
    Atom,
    Other,
}

#[derive(Debug)]
pub enum NameParent<'db> {
    NameDef(NameDef<'db>),
    Atom(Atom<'db>),
    Primary(Primary<'db>),
    PrimaryTarget(PrimaryTarget<'db>),
    Kwarg(Kwarg<'db>),
    KeywordPattern(KeywordPattern<'db>),
    ImportFromAsName(ImportFromAsName<'db>),
    DottedImportName(DottedImportName<'db>),
    DottedPatternName(DottedPatternName<'db>),
    FStringConversion(FStringConversion<'db>),
    Error,
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

    pub fn parse(&self) -> num_bigint::BigInt {
        self.parse_as_big_uint().into()
    }

    pub fn parse_as_big_uint(&self) -> num_bigint::BigUint {
        let mut to_be_parsed = self.as_code();
        let tmp;
        if to_be_parsed.contains('_') {
            tmp = to_be_parsed.replace('_', "");
            to_be_parsed = &tmp;
        }
        use num_traits::Num;
        if let Some(stripped) = to_be_parsed.strip_prefix('0') {
            let base = match stripped.as_bytes().first() {
                None => return 0usize.into(),
                Some(b'x' | b'X') => 16,
                Some(b'o' | b'O') => 8,
                Some(b'b' | b'B') => 2,
                Some(b'0') => return 0usize.into(),
                _ => unreachable!("{stripped}"),
            };
            num_bigint::BigUint::from_str_radix(&stripped[1..], base).unwrap()
        } else {
            to_be_parsed.parse().unwrap()
        }
    }
}

#[derive(Debug)]
pub enum DefiningStmt<'db> {
    FunctionDef(FunctionDef<'db>),
    ClassDef(ClassDef<'db>),
    Assignment(Assignment<'db>),
    ImportName(ImportName<'db>),
    ImportFromAsName(ImportFromAsName<'db>),
    Lambda(Lambda<'db>),
    Comprehension(Comprehension<'db>),
    DictComprehension(DictComprehension<'db>),
    Walrus(Walrus<'db>),
    TryStmt(TryStmt<'db>),
    ForStmt(ForStmt<'db>),
    WithItem(WithItem<'db>),
    DelStmt(DelStmt<'db>),
    MatchStmt(MatchStmt<'db>),
    TypeAlias(TypeAlias<'db>),
    GlobalStmt(GlobalStmt<'db>),
    NonlocalStmt(NonlocalStmt<'db>),
    Error(Error<'db>),
}

impl DefiningStmt<'_> {
    #[inline]
    pub fn index(&self) -> NodeIndex {
        match self {
            DefiningStmt::FunctionDef(n) => n.index(),
            DefiningStmt::ClassDef(n) => n.index(),
            DefiningStmt::Assignment(n) => n.index(),
            DefiningStmt::ImportName(n) => n.index(),
            DefiningStmt::ImportFromAsName(imp) => imp.index(),
            DefiningStmt::Lambda(n) => n.index(),
            DefiningStmt::Comprehension(n) => n.index(),
            DefiningStmt::DictComprehension(n) => n.index(),
            DefiningStmt::Walrus(n) => n.index(),
            DefiningStmt::TryStmt(n) => n.index(),
            DefiningStmt::ForStmt(n) => n.index(),
            DefiningStmt::WithItem(w) => w.index(),
            DefiningStmt::DelStmt(d) => d.index(),
            DefiningStmt::MatchStmt(m) => m.index(),
            DefiningStmt::TypeAlias(a) => a.index(),
            DefiningStmt::GlobalStmt(g) => g.index(),
            DefiningStmt::NonlocalStmt(n) => n.index(),
            DefiningStmt::Error(e) => e.index(),
        }
    }
}

#[derive(Debug)]
pub enum TypeLike<'db> {
    Assignment(Assignment<'db>),
    ClassDef(ClassDef<'db>),
    Function(FunctionDef<'db>),
    ParamName(Option<Annotation<'db>>),
    ImportFromAsName(ImportFromAsName<'db>),
    DottedAsName(DottedAsName<'db>),
    TypeAlias(TypeAlias<'db>),
    TypeParam(TypeParam<'db>),
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
    pub fn iter_stmt_likes(&self) -> StmtLikeIterator<'db> {
        StmtLikeIterator::from_stmt_iterator(self.node, self.node.iter_children())
    }

    pub fn docstring(&self) -> Option<Strings<'db>> {
        let first = self.iter_stmt_likes().next()?;
        first.node.maybe_string()
    }

    pub fn clean_docstring(&self) -> Cow<'db, str> {
        self.docstring()
            .and_then(|d| d.clean_docstring())
            .unwrap_or(Cow::Borrowed(""))
    }
}

impl<'db> List<'db> {
    pub fn unpack(&self) -> StarLikeExpressionIterator<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(star_named_expressions)) {
            StarLikeExpressionIterator::Elements(n.iter_children().step_by(2))
        } else {
            assert_eq!(n.type_(), PyNodeType::Keyword);
            StarLikeExpressionIterator::Empty
        }
    }
    pub fn node_index_range(&self) -> std::ops::Range<NodeIndex> {
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap().index;
        let second = iterator.next().unwrap();
        if second.is_type(Nonterminal(star_named_expressions)) {
            first..iterator.next().unwrap().index
        } else {
            first..second.index
        }
    }
}

impl<'db> Set<'db> {
    pub fn unpack(&self) -> StarLikeExpressionIterator<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(star_named_expressions)) {
            StarLikeExpressionIterator::Elements(n.iter_children().step_by(2))
        } else {
            assert_eq!(n.type_(), PyNodeType::Keyword);
            StarLikeExpressionIterator::Empty
        }
    }
}

pub enum StarLikeExpression<'db> {
    Expression(Expression<'db>),
    NamedExpression(NamedExpression<'db>),
    StarExpression(StarExpression<'db>),
    StarNamedExpression(StarNamedExpression<'db>),
}

impl StarLikeExpression<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Expression(expr) => expr.index(),
            Self::NamedExpression(n) => n.index(),
            Self::StarExpression(s) => s.index(),
            Self::StarNamedExpression(s) => s.index(),
        }
    }
}

impl<'db> Tuple<'db> {
    pub fn iter(&self) -> StarLikeExpressionIterator<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(tuple_content)) {
            StarLikeExpressionIterator::Elements(n.iter_children().step_by(2))
        } else {
            debug_assert_eq!(n.as_code(), ")");
            StarLikeExpressionIterator::Empty
        }
    }
}

pub trait ClonableTupleIterator<'x>: Iterator<Item = StarLikeExpression<'x>> + Clone {}

impl<'db> ClonableTupleIterator<'db> for StarLikeExpressionIterator<'db> {}
impl<'db> ClonableTupleIterator<'db> for StarExpressionsIterator<'db> {}

#[derive(Debug, Clone)]
pub enum StarLikeExpressionIterator<'db> {
    Elements(StepBy<SiblingIterator<'db>>),
    Empty,
}

impl<'db> Iterator for StarLikeExpressionIterator<'db> {
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

#[derive(Clone)]
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
                    DictElement::Star(DictStarred::new(node))
                }
            }),
            DictElementIterator::Empty => None,
        }
    }
}

pub enum DictElement<'db> {
    KeyValue(DictKeyValue<'db>),
    Star(DictStarred<'db>),
}

impl<'db> DictKeyValue<'db> {
    pub fn key(self) -> Expression<'db> {
        Expression::new(self.node.nth_child(0))
    }

    pub fn value(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(2))
    }
}

impl<'db> DictStarred<'db> {
    pub fn expression_part(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.nth_child(1))
    }
}

impl<'db> Expression<'db> {
    pub fn unpack(self) -> ExpressionContent<'db> {
        let node = self.node.nth_child(0);
        if node.is_type(Nonterminal(lambda)) {
            ExpressionContent::Lambda(Lambda::new(node))
        } else if node.is_type(Nonterminal(ternary)) {
            ExpressionContent::Ternary(Ternary::new(node))
        } else {
            ExpressionContent::ExpressionPart(ExpressionPart::new(node))
        }
    }

    pub fn is_lambda(&self) -> bool {
        let node = self.node.nth_child(0);
        node.is_type(Nonterminal(lambda))
    }

    pub fn maybe_string(&self) -> Option<Strings<'db>> {
        match self.maybe_unpacked_atom()? {
            AtomContent::Strings(s) => Some(s),
            _ => None,
        }
    }

    pub fn is_string(&self) -> bool {
        self.maybe_string().is_some()
    }

    pub fn search_names(&self) -> NameIterator<'db> {
        NameIterator(self.node.search(&[Terminal(TerminalType::Name)], false))
    }

    fn maybe_name_or_last_primary_name(&self) -> Option<NameOrPrimaryWithNames<'db>> {
        match self.unpack() {
            ExpressionContent::ExpressionPart(ExpressionPart::Atom(a)) => {
                if let AtomContent::Name(n) = a.unpack() {
                    Some(NameOrPrimaryWithNames::Name(n))
                } else {
                    None
                }
            }
            ExpressionContent::ExpressionPart(ExpressionPart::Primary(p)) => p
                .is_only_attributes()
                .then_some(NameOrPrimaryWithNames::PrimaryWithNames(p)),
            _ => None,
        }
    }

    pub fn is_literal_value(&self) -> bool {
        match self.unpack() {
            ExpressionContent::ExpressionPart(ExpressionPart::Atom(atom_)) => {
                atom_.is_literal_value()
            }
            _ => false,
        }
    }

    pub fn is_none_literal(&self) -> bool {
        matches!(self.maybe_unpacked_atom(), Some(AtomContent::NoneLiteral))
    }

    pub fn maybe_unpacked_atom(&self) -> Option<AtomContent<'db>> {
        match self.unpack() {
            ExpressionContent::ExpressionPart(expr_part) => expr_part.maybe_unpacked_atom(),
            _ => None,
        }
    }

    pub fn maybe_simple_int(&self) -> Option<num_bigint::BigUint> {
        match self.maybe_unpacked_atom()? {
            AtomContent::Int(i) => Some(i.parse_as_big_uint()),
            _ => None,
        }
    }

    pub fn maybe_simple_bool(&self) -> Option<bool> {
        match self.maybe_unpacked_atom()? {
            AtomContent::Bool(b) => Some(b.as_code() == "True"),
            _ => None,
        }
    }

    pub fn maybe_tuple(&self) -> Option<Tuple<'db>> {
        match self.maybe_unpacked_atom() {
            Some(AtomContent::Tuple(t)) => Some(t),
            _ => None,
        }
    }

    pub fn maybe_single_string_literal(&self) -> Option<StringLiteral<'db>> {
        self.maybe_unpacked_atom()
            .and_then(|a| a.maybe_single_string_literal())
    }

    pub fn is_ellipsis_literal(&self) -> bool {
        matches!(self.maybe_unpacked_atom(), Some(AtomContent::Ellipsis))
    }

    pub fn in_simple_assignment(&self) -> Option<NameDef<'db>> {
        in_simple_assignment(self.node)
    }
}

pub enum ExpressionContent<'db> {
    ExpressionPart(ExpressionPart<'db>),
    Ternary(Ternary<'db>),
    Lambda(Lambda<'db>),
}

#[derive(Debug, Copy, Clone)]
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
    Comparisons(Comparisons<'db>),
    Inversion(Inversion<'db>),
    Conjunction(Conjunction<'db>),
    Disjunction(Disjunction<'db>),
}

pub enum NameOrPrimaryWithNames<'db> {
    Name(Name<'db>),
    PrimaryWithNames(Primary<'db>),
}

impl NameOrPrimaryWithNames<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Name(n) => n.index(),
            Self::PrimaryWithNames(p) => p.index(),
        }
    }
}

macro_rules! for_each_expr_part {
    ($name:ident, $return_type:ty) => {
        pub fn $name(&self) -> $return_type {
            match self {
                Self::Atom(n) => n.$name(),
                Self::Primary(n) => n.$name(),
                Self::AwaitPrimary(n) => n.$name(),
                Self::Power(n) => n.$name(),
                Self::Factor(n) => n.$name(),
                Self::Term(n) => n.$name(),
                Self::Sum(n) => n.$name(),
                Self::ShiftExpr(n) => n.$name(),
                Self::BitwiseAnd(n) => n.$name(),
                Self::BitwiseXor(n) => n.$name(),
                Self::BitwiseOr(n) => n.$name(),
                Self::Comparisons(n) => n.$name(),
                Self::Inversion(n) => n.$name(),
                Self::Conjunction(n) => n.$name(),
                Self::Disjunction(n) => n.$name(),
            }
        }
    };
}

impl<'db> ExpressionPart<'db> {
    fn new(node: PyNode<'db>) -> Self {
        Self::maybe_new(node).unwrap()
    }

    fn maybe_new(node: PyNode<'db>) -> Option<Self> {
        // Sorted by how often they probably appear
        Some(if node.is_type(Nonterminal(atom)) {
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
            Self::Comparisons(Comparisons::new(node))
        } else if node.is_type(Nonterminal(inversion)) {
            Self::Inversion(Inversion::new(node))
        } else if node.is_type(Nonterminal(conjunction)) {
            Self::Conjunction(Conjunction::new(node))
        } else if node.is_type(Nonterminal(disjunction)) {
            Self::Disjunction(Disjunction::new(node))
        } else {
            return None;
        })
    }

    for_each_expr_part!(index, NodeIndex);
    for_each_expr_part!(as_code, &'db str);
    for_each_expr_part!(start, CodeIndex);
    for_each_expr_part!(end, CodeIndex);

    pub fn maybe_unpacked_atom(&self) -> Option<AtomContent<'db>> {
        match self {
            Self::Atom(a) => Some(a.unpack()),
            _ => None,
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
            Self::Comparisons(n) => n.search_interesting_nodes(),
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
            NamedExpressionContent::Walrus(walrus_) => walrus_.expression(),
        }
    }

    pub fn unpack(self) -> NamedExpressionContent<'db> {
        let node = self.node.nth_child(0);
        if node.is_type(Nonterminal(expression)) {
            NamedExpressionContent::Expression(Expression::new(node))
        } else {
            NamedExpressionContent::Walrus(Walrus::new(node))
        }
    }

    pub fn is_ellipsis_literal(&self) -> bool {
        if let NamedExpressionContent::Expression(e) = self.unpack() {
            e.is_ellipsis_literal()
        } else {
            false
        }
    }

    pub fn maybe_single_string_literal(&self) -> Option<StringLiteral<'db>> {
        if let NamedExpressionContent::Expression(e) = self.unpack() {
            e.maybe_single_string_literal()
        } else {
            None
        }
    }

    pub fn has_await(&self) -> bool {
        node_subtree_has_await(self.node)
    }
}

fn node_subtree_has_await(node: PyNode) -> bool {
    node.search(&[Nonterminal(await_primary)], true)
        .next()
        .is_some()
}

pub enum NamedExpressionContent<'db> {
    Expression(Expression<'db>),
    Walrus(Walrus<'db>),
}

impl<'db> Walrus<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(self.node.nth_child(0))
    }

    pub fn unpack(&self) -> (NameDef<'db>, Expression<'db>) {
        let mut iterator = self.node.iter_children();
        let name_d = iterator.next().unwrap();
        iterator.next();
        let expr = iterator.next().unwrap();
        (NameDef::new(name_d), Expression::new(expr))
    }

    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(2))
    }
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

impl<'db> BrokenScope<'db> {
    pub fn iter_stmt_likes(&self) -> StmtLikeIterator<'db> {
        let mut iterator = self.node.iter_children();
        let indent_leaf = iterator.next().unwrap(); // get rid of indent leaf
        StmtLikeIterator::from_stmt_iterator(indent_leaf, iterator)
    }
}

impl<'db> Block<'db> {
    pub fn iter_stmt_likes(&self) -> StmtLikeIterator<'db> {
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap();
        if first.is_type(Nonterminal(simple_stmts)) {
            StmtLikeIterator {
                stmts: SiblingIterator::new_empty(&first),
                simple_stmts: first.iter_children().step_by(2),
            }
        } else {
            iterator.next(); // get rid of indent leaf
            StmtLikeIterator::from_stmt_iterator(first, iterator)
        }
    }

    pub fn last_leaf_index(&self) -> NodeIndex {
        self.node.last_leaf_in_subtree().index
    }
}

impl<'db> ElseBlock<'db> {
    pub fn block(&self) -> Block<'db> {
        Block::new(self.node.nth_child(2))
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
        // with_stmt: "with" with_items block ":"
        let mut iterator = self.node.iter_children().skip(1);
        let with = WithItems::new(iterator.next().unwrap());
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
        (
            Expression::new(expr),
            iterator.next().map(Target::new_non_iterator),
        )
    }

    pub fn in_async_with_stmt(&self) -> bool {
        let with = self.node.parent().unwrap().parent().unwrap();
        with.is_type(Nonterminal(async_stmt))
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
    Else(ElseBlock<'db>),
}

impl IfBlockType<'_> {
    pub fn first_leaf_index(&self) -> NodeIndex {
        match self {
            Self::If(named_expr, _) => named_expr.index() - 1, // The if/elif
            Self::Else(else_) => else_.index(),
        }
    }
}

#[derive(Clone)]
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
                return Some(Self::Item::Else(ElseBlock::new(n)));
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
    ExceptStar(ExceptStarBlock<'db>),
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
            } else if n.is_type(Nonterminal(except_star_block)) {
                return Some(TryBlockType::ExceptStar(ExceptStarBlock::new(n)));
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
    pub fn unpack(&self) -> (Option<ExceptExpression<'db>>, Block<'db>) {
        // "except" [except_expression] ":" block
        let mut iterator = self.node.iter_children().skip(1);
        let except_expr = iterator.next().unwrap();
        if except_expr.is_leaf() {
            (None, Block::new(iterator.next().unwrap()))
        } else {
            iterator.next();
            let block_ = Block::new(iterator.next().unwrap());

            (Some(ExceptExpression::new(except_expr)), block_)
        }
    }
}

impl<'db> ExceptStarBlock<'db> {
    pub fn unpack(&self) -> (ExceptExpression<'db>, Block<'db>) {
        // "except" "*" except_expression ":" block
        let mut iterator = self.node.iter_children().skip(2);
        let except_expr = iterator.next().unwrap();
        iterator.next();
        let block_ = Block::new(iterator.next().unwrap());
        (ExceptExpression::new(except_expr), block_)
    }
}

impl<'db> ExceptExpression<'db> {
    pub fn unpack(&self) -> ExceptExpressionContent<'db> {
        // except_expression: [expression ["as" name_def]]
        let mut clause_iterator = self.node.iter_children();
        let first = clause_iterator.next().unwrap();
        clause_iterator.next();
        if let Some(as_name) = clause_iterator.next() {
            ExceptExpressionContent::WithNameDef(Expression::new(first), NameDef::new(as_name))
        } else {
            ExceptExpressionContent::Expressions(Expressions::new(first))
        }
    }
}

pub enum ExceptExpressionContent<'db> {
    WithNameDef(Expression<'db>, NameDef<'db>),
    Expressions(Expressions<'db>),
}

#[derive(Debug, Copy, Clone)]
pub enum StmtLikeContent<'db> {
    // From simple_stmt
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
    TypeAlias(TypeAlias<'db>),
    // From stmt
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
    Error(Error<'db>),
    BrokenScope(BrokenScope<'db>),
    Newline,
}

impl<'db> StmtLikeContent<'db> {
    fn from_simple_stmt(simple: PyNode<'db>) -> Self {
        let simple_child = simple.nth_child(0);
        if simple_child.is_type(Nonterminal(assignment)) {
            Self::Assignment(Assignment::new(simple_child))
        } else if simple_child.is_type(Nonterminal(star_expressions)) {
            Self::StarExpressions(StarExpressions::new(simple_child))
        } else if simple_child.is_type(Nonterminal(return_stmt)) {
            Self::ReturnStmt(ReturnStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(yield_expr)) {
            Self::YieldExpr(YieldExpr::new(simple_child))
        } else if simple_child.is_type(Nonterminal(raise_stmt)) {
            Self::RaiseStmt(RaiseStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_from)) {
            Self::ImportFrom(ImportFrom::new(simple_child))
        } else if simple_child.is_type(Nonterminal(import_name)) {
            Self::ImportName(ImportName::new(simple_child))
        } else if simple_child.is_type(Nonterminal(pass_stmt)) {
            Self::PassStmt(PassStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(global_stmt)) {
            Self::GlobalStmt(GlobalStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(nonlocal_stmt)) {
            Self::NonlocalStmt(NonlocalStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(assert_stmt)) {
            Self::AssertStmt(AssertStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(break_stmt)) {
            Self::BreakStmt(BreakStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(continue_stmt)) {
            Self::ContinueStmt(ContinueStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(del_stmt)) {
            Self::DelStmt(DelStmt::new(simple_child))
        } else if simple_child.is_type(Nonterminal(type_alias)) {
            Self::TypeAlias(TypeAlias::new(simple_child))
        } else {
            unreachable!()
        }
    }

    fn from_stmt_child(child: PyNode<'db>) -> Self {
        if child.is_type(Nonterminal(function_def)) {
            Self::FunctionDef(FunctionDef::new(child))
        } else if child.is_type(Nonterminal(class_def)) {
            Self::ClassDef(ClassDef::new(child))
        } else if child.is_type(Nonterminal(decorated)) {
            Self::Decorated(Decorated::new(child))
        } else if child.is_type(Nonterminal(if_stmt)) {
            Self::IfStmt(IfStmt::new(child))
        } else if child.is_type(Nonterminal(try_stmt)) {
            Self::TryStmt(TryStmt::new(child))
        } else if child.is_type(Nonterminal(for_stmt)) {
            Self::ForStmt(ForStmt::new(child))
        } else if child.is_type(Nonterminal(while_stmt)) {
            Self::WhileStmt(WhileStmt::new(child))
        } else if child.is_type(Nonterminal(with_stmt)) {
            Self::WithStmt(WithStmt::new(child))
        } else if child.is_type(Nonterminal(match_stmt)) {
            Self::MatchStmt(MatchStmt::new(child))
        } else if child.is_type(Nonterminal(async_stmt)) {
            Self::AsyncStmt(AsyncStmt::new(child))
        } else if child.is_type(Nonterminal(broken_scope)) {
            Self::BrokenScope(BrokenScope::new(child))
        } else {
            debug_assert_eq!(child.type_(), Terminal(TerminalType::Newline));
            Self::Newline
        }
    }

    pub fn maybe_simple_expr(&self) -> Option<Expression<'db>> {
        match self {
            StmtLikeContent::StarExpressions(star_exprs) => star_exprs.maybe_simple_expression(),
            _ => None,
        }
    }

    pub fn maybe_string(&self) -> Option<Strings<'db>> {
        self.maybe_simple_expr()?.maybe_string()
    }
}

#[derive(Clone)]
pub struct StmtLikeIterator<'db> {
    stmts: SiblingIterator<'db>,
    simple_stmts: StepBy<SiblingIterator<'db>>,
}

impl<'db> StmtLikeIterator<'db> {
    #[inline]
    fn from_stmt_iterator(base_node: PyNode<'db>, iterator: SiblingIterator<'db>) -> Self {
        Self {
            stmts: iterator,
            simple_stmts: SiblingIterator::new_empty(&base_node).step_by(2),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct StmtLikeIteratorItem<'db> {
    pub parent_index: NodeIndex,
    pub node: StmtLikeContent<'db>,
}

impl<'db> Iterator for StmtLikeIterator<'db> {
    type Item = StmtLikeIteratorItem<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.simple_stmts.next() {
            if node.is_type(Terminal(TerminalType::Newline)) {
                return self.next();
            }
            return Some(StmtLikeIteratorItem {
                parent_index: node.index,
                node: StmtLikeContent::from_simple_stmt(node),
            });
        }
        let s = self.stmts.next()?;
        if s.is_type(Nonterminal(stmt)) {
            let child = s.nth_child(0);
            if child.is_type(Nonterminal(simple_stmts)) {
                self.simple_stmts = child.iter_children().step_by(2);
                self.next()
            } else {
                Some(StmtLikeIteratorItem {
                    parent_index: s.index,
                    node: StmtLikeContent::from_stmt_child(child),
                })
            }
        } else if s.is_error_recovery_node() {
            Some(StmtLikeIteratorItem {
                parent_index: s.index,
                node: StmtLikeContent::Error(Error::new(s)),
            })
        } else {
            debug_assert!(
                s.is_type(Terminal(TerminalType::Dedent))
                    || s.is_type(Terminal(TerminalType::Endmarker)),
                "{s:?}",
            );
            None
        }
    }
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

    pub fn end_position_last_leaf(&self) -> CodeIndex {
        let mut leaf = self.node.last_leaf_in_subtree();
        while leaf.is_type(Terminal(TerminalType::Newline))
            || leaf.is_type(Terminal(TerminalType::Dedent))
        {
            leaf = leaf.previous_leaf().unwrap();
        }
        leaf.end()
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

    pub fn iter_reverse(&self) -> ReverseDecoratorIterator<'db> {
        let current_node = Some(self.node.iter_children().last().unwrap());
        ReverseDecoratorIterator { current_node }
    }
}

pub struct DecoratorIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for DecoratorIterator<'db> {
    type Item = Decorator<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Self::Item::new)
    }
}

pub struct ReverseDecoratorIterator<'db> {
    current_node: Option<PyNode<'db>>,
}

impl<'db> Iterator for ReverseDecoratorIterator<'db> {
    type Item = Decorator<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current_node.take();
        if let Some(current) = current {
            self.current_node = current.previous_sibling();
        }
        current.map(Self::Item::new)
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

    pub fn maybe_simple_expression(&self) -> Option<Expression<'db>> {
        match self.unpack() {
            StarExpressionContent::Expression(expr) => Some(expr),
            _ => None,
        }
    }

    pub fn is_none_literal(&self) -> bool {
        self.maybe_simple_expression()
            .is_some_and(|e| e.is_none_literal())
    }
}

pub enum StarExpressionContent<'db> {
    Expression(Expression<'db>),
    StarExpression(StarExpression<'db>),
    Tuple(StarExpressionsTuple<'db>),
}

impl<'db> StarExpression<'db> {
    pub fn expression_part(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.nth_child(1))
    }
}

impl<'db> StarNamedExpression<'db> {
    pub fn expression_part(&self) -> ExpressionPart<'db> {
        // TODO this is completely wrong.
        ExpressionPart::new(self.node.nth_child(1))
    }
}

impl<'db> Comprehension<'db> {
    pub fn unpack(&self) -> (NamedExpression<'db>, ForIfClauses<'db>) {
        let mut iter = self.node.iter_children();
        (
            NamedExpression::new(iter.next().unwrap()),
            ForIfClauses::new(iter.next().unwrap()),
        )
    }

    pub fn is_generator(&self) -> bool {
        self.node.previous_leaf().unwrap().as_code() == "("
    }
}

impl<'db> DictComprehension<'db> {
    pub fn unpack(&self) -> (DictKeyValue<'db>, ForIfClauses<'db>) {
        let mut iter = self.node.iter_children();
        (
            DictKeyValue::new(iter.next().unwrap()),
            ForIfClauses::new(iter.next().unwrap()),
        )
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

impl ForIfClause<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Async(s) | Self::Sync(s) => s.index(),
        }
    }
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

    pub fn has_await(&self) -> bool {
        node_subtree_has_await(self.node)
    }
}

pub struct CompIfIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for CompIfIterator<'db> {
    type Item = CompIf<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Self::Item::new)
    }
}

impl<'db> CompIf<'db> {
    pub fn expression_part(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.nth_child(1))
    }

    pub fn has_await(&self) -> bool {
        node_subtree_has_await(self.node)
    }
}

impl<'db> ClassDef<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(self.node.nth_child(1))
    }

    pub fn name(&self) -> Name<'db> {
        self.name_def().name()
    }

    pub fn arguments(&self) -> Option<Arguments<'db>> {
        let mut args = self.node.nth_child(3);
        if args.is_leaf() {
            args = args.next_sibling().unwrap();
        }
        args.is_type(Nonterminal(arguments))
            .then(|| Arguments::new(args))
    }

    pub fn unpack(&self) -> (Option<TypeParams<'db>>, Option<Arguments<'db>>, Block<'db>) {
        let mut args = None;
        let mut type_params_ = None;
        for child in self.node.iter_children().skip(2) {
            if child.is_type(Nonterminal(arguments)) {
                args = Some(Arguments::new(child));
            } else if child.is_type(Nonterminal(type_params)) {
                type_params_ = Some(TypeParams::new(child));
            } else if child.is_type(Nonterminal(block)) {
                return (type_params_, args, Block::new(child));
            }
        }
        unreachable!()
    }

    pub fn type_params(&self) -> Option<TypeParams<'db>> {
        let n = self.node.nth_child(2);
        n.is_type(Nonterminal(type_params))
            .then(|| TypeParams::new(n))
    }

    pub fn block(&self) -> Block<'db> {
        Block::new(self.node.iter_children().last().unwrap())
    }

    pub fn search_potential_self_assignments(&self) -> PotentialSelfAssignments<'db> {
        PotentialSelfAssignments(self.node.search(&[Nonterminal(t_primary)], true))
    }

    pub fn maybe_decorated(&self) -> Option<Decorated<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(decorated)) {
            Some(Decorated::new(parent))
        } else {
            debug_assert_eq!(parent.type_(), Nonterminal(stmt));
            None
        }
    }

    pub fn docstring(&self) -> Option<Strings<'db>> {
        self.block().iter_stmt_likes().next()?.node.maybe_string()
    }
}

pub struct PotentialSelfAssignments<'db>(SearchIterator<'db>);

impl<'db> Iterator for PotentialSelfAssignments<'db> {
    type Item = (Name<'db>, Name<'db>);
    fn next(&mut self) -> Option<Self::Item> {
        for node in &mut self.0 {
            let name_d = node.nth_child(2);
            if name_d.is_type(Nonterminal(name_def)) {
                let atom_ = node.nth_child(0);
                if atom_.is_type(Nonterminal(atom)) {
                    let self_name = atom_.nth_child(0);
                    if self_name.is_type(Terminal(TerminalType::Name)) {
                        return Some((Name::new(self_name), NameDef::new(name_d).name()));
                    }
                }
            }
        }
        None
    }
}

impl<'db> FunctionDef<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(self.node.nth_child(1))
    }

    pub fn name(&self) -> Name<'db> {
        self.name_def().name()
    }

    pub fn end_position_of_colon(&self) -> CodeIndex {
        for child in self.node.iter_children().skip(3) {
            if child.is_leaf() {
                debug_assert_eq!(child.as_code(), ":");
                return child.end();
            }
        }
        unreachable!()
    }

    pub fn return_annotation(&self) -> Option<ReturnAnnotation<'db>> {
        for child in self.node.iter_children().skip(2) {
            if child.is_type(Nonterminal(return_annotation)) {
                return Some(ReturnAnnotation::new(child));
            }
        }
        None
    }

    pub fn colon_index(&self) -> NodeIndex {
        for child in self.node.iter_children().skip(2) {
            if child.as_code() == ":" {
                return child.index;
            }
        }
        unreachable!()
    }

    pub fn is_typed(&self) -> bool {
        // A function is considered typed according to Mypy if at least param or return annotation
        // is used.
        self.return_annotation().is_some() || self.has_param_annotations()
    }

    pub fn has_param_annotations(&self) -> bool {
        self.params().iter().any(|p| p.annotation().is_some())
    }

    pub fn type_params(&self) -> Option<TypeParams<'db>> {
        let n = self.node.nth_child(2);
        n.is_type(Nonterminal(type_params))
            .then(|| TypeParams::new(n))
    }

    pub fn params(&self) -> FunctionDefParameters<'db> {
        let mut n = self.node.nth_child(2);
        if n.is_type(Nonterminal(type_params)) {
            n = n.next_sibling().unwrap();
        }
        FunctionDefParameters::new(n)
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
            FunctionParent::DecoratedAsync(Decorated::new(parent.parent().unwrap()))
        } else {
            unreachable!()
        }
    }

    pub fn parent_scope(&self) -> Scope<'db> {
        scope_for_node(self.node)
    }

    pub fn maybe_decorated(&self) -> Option<Decorated<'db>> {
        match self.parent() {
            FunctionParent::Decorated(dec) | FunctionParent::DecoratedAsync(dec) => Some(dec),
            _ => None,
        }
    }

    pub fn in_conditional_scope(&self) -> bool {
        let parent_block = self.node.parent_until(&[Nonterminal(block)]);
        parent_block.is_some_and(|block_| {
            let parent = block_.parent().unwrap();
            parent.is_type(Nonterminal(if_stmt)) || parent.is_type(Nonterminal(else_block))
        })
    }

    pub fn unpack(
        &self,
    ) -> (
        NameDef<'db>,
        Option<TypeParams<'db>>,
        FunctionDefParameters<'db>,
        Option<ReturnAnnotation<'db>>,
        Block<'db>,
    ) {
        // function_def: "def" name_def function_def_parameters
        //               return_annotation? ":" block
        let mut iterator = self.node.iter_children();
        iterator.next(); // Skip "def"
        let name_d = NameDef::new(iterator.next().unwrap());
        let mut next = iterator.next().unwrap();
        let mut type_params_ = None;
        if next.is_type(Nonterminal(type_params)) {
            type_params_ = Some(TypeParams::new(next));
            next = iterator.next().unwrap();
        }
        let params = FunctionDefParameters::new(next);
        let mut ret_annot = iterator.next();
        if ret_annot.unwrap().is_type(Nonterminal(return_annotation)) {
            iterator.next();
        } else {
            ret_annot = None;
        }
        (
            name_d,
            type_params_,
            params,
            ret_annot.map(ReturnAnnotation::new),
            Block::new(iterator.next().unwrap()),
        )
    }

    pub fn body(&self) -> Block<'db> {
        Block::new(self.node.iter_children().last().unwrap())
    }

    pub fn on_name_def_in_scope(&self, callback: &mut impl FnMut(NameDef<'db>)) {
        for p in self.params().iter() {
            callback(p.name_def())
        }
        const SEARCH_NAME_DEFS: &[PyNodeType] = &[
            Nonterminal(name_def),
            Nonterminal(function_def),
            Nonterminal(class_def),
            Nonterminal(lambda),
            Nonterminal(t_primary),
        ];
        for node in self.body().node.search(SEARCH_NAME_DEFS, true) {
            if node.is_type(Nonterminal(name_def)) {
                callback(NameDef::new(node))
            } else if node.is_type(Nonterminal(function_def)) {
                callback(FunctionDef::new(node).name_def())
            } else if node.is_type(Nonterminal(class_def)) {
                callback(ClassDef::new(node).name_def())
            }
        }
    }

    pub fn docstring(&self) -> Option<Strings<'db>> {
        self.body().iter_stmt_likes().next()?.node.maybe_string()
    }

    pub fn trivial_body_state(&self) -> TrivialBodyState<'_> {
        // In Mypy this is handled in "is_trivial_body"
        let mut stmts = self.body().iter_stmt_likes();
        let mut stmt_like = stmts.next().unwrap();
        // Skip the first docstring
        if stmt_like.node.maybe_string().is_some() {
            let Some(s) = stmts.next() else {
                return TrivialBodyState::Known(true); // It was simply a docstring
            };
            stmt_like = s
        }

        TrivialBodyState::Known(match stmt_like.node {
            StmtLikeContent::PassStmt(_) => true,
            StmtLikeContent::StarExpressions(star_exprs) => star_exprs
                .maybe_simple_expression()
                .is_some_and(|expr| expr.is_string() || expr.is_ellipsis_literal()),
            StmtLikeContent::RaiseStmt(raise_stmt_) => {
                if let Some((expr, _)) = raise_stmt_.unpack() {
                    return TrivialBodyState::RaiseExpr(expr);
                }
                false
            }
            _ => false,
        })
    }
}

pub enum TrivialBodyState<'db> {
    Known(bool),
    RaiseExpr(Expression<'db>),
}

pub enum FunctionParent<'db> {
    Decorated(Decorated<'db>),
    Async,
    DecoratedAsync(Decorated<'db>),
    Normal,
}

impl FunctionParent<'_> {
    pub fn is_async(&self) -> bool {
        matches!(self, Self::Async | Self::DecoratedAsync(_))
    }
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

#[derive(Clone)]
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
                    use ParamKind::*;
                    if node.is_type(Nonterminal(param_no_default))
                        || node.is_type(Nonterminal(param_with_default))
                        || node.is_type(Nonterminal(lambda_param_no_default))
                        || node.is_type(Nonterminal(lambda_param_with_default))
                    {
                        return Some(Self::Item::new(
                            &mut node.iter_children(),
                            if *positional_only {
                                PositionalOnly
                            } else {
                                PositionalOrKeyword
                            },
                        ));
                    } else if node.is_type(Nonterminal(star_etc))
                        || node.is_type(Nonterminal(lambda_star_etc))
                    {
                        *self = Self::Iterator(node.iter_children(), false);
                        return self.next();
                    } else if node.is_type(Nonterminal(param_maybe_default))
                        || node.is_type(Nonterminal(lambda_param_maybe_default))
                    {
                        debug_assert!(!*positional_only);
                        return Some(Self::Item::new(&mut node.iter_children(), KeywordOnly));
                    } else if node.is_type(Nonterminal(starred_param))
                        || node.is_type(Nonterminal(lambda_starred_param))
                    {
                        return Some(Self::Item::new(&mut node.iter_children().skip(1), Star));
                    } else if node.is_type(Nonterminal(double_starred_param))
                        || node.is_type(Nonterminal(lambda_double_starred_param))
                    {
                        return Some(Self::Item::new(&mut node.iter_children().skip(1), StarStar));
                    } else {
                        debug_assert!(
                            [",", "*", "/"].contains(&node.as_code()),
                            "{}",
                            node.as_code()
                        );
                        if node.as_code() == "/" {
                            *positional_only = false;
                        }
                    }
                }
                None
            }
            Self::Finished => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Param<'db> {
    kind: ParamKind,
    name_def: NameDef<'db>,
    annotation: Option<ParamAnnotation<'db>>,
    default: Option<Expression<'db>>,
}

#[derive(Debug, Clone, Copy)]
pub enum ParamAnnotation<'db> {
    Annotation(Annotation<'db>),
    StarAnnotation(StarAnnotation<'db>),
}

impl<'db> ParamAnnotation<'db> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Annotation(a) => a.index(),
            Self::StarAnnotation(s) => s.index(),
        }
    }

    pub fn maybe_starred(&self) -> Result<StarExpression<'db>, Expression<'db>> {
        match self {
            Self::Annotation(annot) => Err(annot.expression()),
            Self::StarAnnotation(star_annot) => match star_annot.unpack() {
                StarAnnotationContent::Expression(e) => Err(e),
                StarAnnotationContent::StarExpression(star_expr) => Ok(star_expr),
            },
        }
    }
}

impl<'db> Param<'db> {
    fn new(param_children: &mut impl Iterator<Item = PyNode<'db>>, kind: ParamKind) -> Self {
        let name_d = NameDef::new(param_children.next().unwrap());
        let annot = if let Some(annotation_node) = param_children.next() {
            if annotation_node.is_type(Nonterminal(annotation)) {
                param_children.next(); // Make sure the next node is skipped for defaults
                Some(ParamAnnotation::Annotation(Annotation::new(
                    annotation_node,
                )))
            } else if annotation_node.is_type(Nonterminal(star_annotation)) {
                param_children.next();
                Some(ParamAnnotation::StarAnnotation(StarAnnotation::new(
                    annotation_node,
                )))
            } else {
                None
            }
        } else {
            None
        };
        let default_node = param_children.next();
        Self {
            kind,
            name_def: name_d,
            annotation: annot,
            default: default_node.map(Expression::new),
        }
    }

    pub fn kind(&self) -> ParamKind {
        self.kind
    }

    pub fn default(&self) -> Option<Expression<'db>> {
        self.default
    }

    pub fn name_def(&self) -> NameDef<'db> {
        self.name_def
    }

    pub fn annotation(&self) -> Option<ParamAnnotation<'db>> {
        self.annotation
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd)]
pub enum ParamKind {
    PositionalOnly,
    PositionalOrKeyword,
    Star,
    KeywordOnly,
    StarStar,
}

impl<'db> Annotation<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }

    pub fn maybe_assignment_name(&self) -> Option<NameDef<'db>> {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(assignment)) {
            let maybe_name_def = parent.nth_child(0).nth_child(0);
            if maybe_name_def.is_type(Nonterminal(name_def)) {
                return Some(NameDef::new(maybe_name_def));
            }
        }
        None
    }
}

pub enum StarAnnotationContent<'db> {
    Expression(Expression<'db>),
    StarExpression(StarExpression<'db>),
}

impl StarAnnotationContent<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            StarAnnotationContent::Expression(e) => e.index(),
            StarAnnotationContent::StarExpression(s) => s.index(),
        }
    }
}

impl<'db> StarAnnotation<'db> {
    pub fn unpack(&self) -> StarAnnotationContent<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(expression)) {
            StarAnnotationContent::Expression(Expression::new(n))
        } else {
            debug_assert_eq!(n.type_(), Nonterminal(star_expression));
            StarAnnotationContent::StarExpression(StarExpression::new(n))
        }
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

impl<'db> ArgumentsDetails<'db> {
    pub fn index(&self) -> Option<NodeIndex> {
        match self {
            Self::None => None,
            Self::Comprehension(comp) => Some(comp.index()),
            Self::Node(arg) => Some(arg.index()),
        }
    }

    pub fn maybe_single_positional(&self) -> Option<NamedExpression<'db>> {
        match self {
            Self::Node(args) => {
                let mut iterator = args.iter();
                let first = iterator.next().unwrap();
                if let Argument::Positional(pos) = first {
                    Some(pos).filter(|_| iterator.next().is_none())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = ArgOrComprehension<'db>> {
        match self {
            ArgumentsDetails::None => AllArgsIterator::None,
            ArgumentsDetails::Comprehension(c) => AllArgsIterator::Comprehension(*c),
            ArgumentsDetails::Node(args) => AllArgsIterator::Args(args.iter()),
        }
    }
}

pub enum ArgOrComprehension<'db> {
    Arg(Argument<'db>),
    Comprehension(Comprehension<'db>),
}

impl ArgOrComprehension<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Arg(arg) => arg.index(),
            Self::Comprehension(comp) => comp.index(),
        }
    }
}

enum AllArgsIterator<'db> {
    None,
    Comprehension(Comprehension<'db>),
    Args(ArgsIterator<'db>),
}

impl<'db> Iterator for AllArgsIterator<'db> {
    type Item = ArgOrComprehension<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::None => None,
            Self::Comprehension(comp) => {
                let x = *comp;
                *self = Self::None;
                Some(Self::Item::Comprehension(x))
            }
            Self::Args(args_iterator) => Some(Self::Item::Arg(args_iterator.next()?)),
        }
    }
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
                return AssignmentContent::Normal(iter, Self::create_right_side(child));
            } else if child.is_type(Nonterminal(annotation)) {
                iterator.next();
                let right = iterator.next().map(Self::create_right_side);
                return AssignmentContent::WithAnnotation(
                    Target::new_single_target(self.node.nth_child(0)),
                    Annotation::new(child),
                    right,
                );
            } else if child.is_type(Nonterminal(augassign)) {
                let right = Self::create_right_side(iterator.next().unwrap());
                return AssignmentContent::AugAssign(
                    Target::new_single_target(self.node.nth_child(0)),
                    AugAssign::new(child),
                    right,
                );
            }
        }
        unreachable!()
    }

    fn create_right_side(child: PyNode) -> AssignmentRightSide {
        if child.is_type(Nonterminal(star_expressions)) {
            AssignmentRightSide::StarExpressions(StarExpressions::new(child))
        } else {
            AssignmentRightSide::YieldExpr(YieldExpr::new(child))
        }
    }

    pub fn right_side(&self) -> Option<AssignmentRightSide<'db>> {
        match self.unpack() {
            AssignmentContent::Normal(_, right) => Some(right),
            AssignmentContent::WithAnnotation(_, _, right) => right,
            AssignmentContent::AugAssign(_, _, right) => Some(right),
        }
    }

    pub fn maybe_annotation(&self) -> Option<Annotation<'db>> {
        let annot = self.node.iter_children().nth(1).unwrap();
        (annot.is_type(Nonterminal(annotation))).then(|| Annotation::new(annot))
    }

    pub fn maybe_simple_type_expression_assignment(
        &self,
    ) -> Option<(NameDef<'db>, Option<Annotation<'db>>, Expression<'db>)> {
        let (mut targets, annot, expr) = self.maybe_simple_targets_expression_assignment()?;
        let first = targets.next().unwrap();
        if targets.next().is_some() {
            return None;
        }
        Some((first, annot, expr))
    }

    fn maybe_simple_targets_expression_assignment(
        &self,
    ) -> Option<(
        impl Iterator<Item = NameDef<'db>>,
        Option<Annotation<'db>>,
        Expression<'db>,
    )> {
        match self.unpack() {
            AssignmentContent::Normal(targets_, right) => {
                for target in targets_.clone() {
                    if !matches!(target, Target::Name(_)) {
                        return None;
                    }
                }
                if let AssignmentRightSide::StarExpressions(star_exprs) = right
                    && let StarExpressionContent::Expression(expr) = star_exprs.unpack()
                {
                    return Some((SimpleNameIterator::Targets(targets_), None, expr));
                }
                None
            }
            AssignmentContent::WithAnnotation(t, annotation_, right) => {
                let name_d = if let Target::Name(name_d) = t {
                    name_d
                } else {
                    return None;
                };
                if let Some(AssignmentRightSide::StarExpressions(star_exprs)) = right
                    && let StarExpressionContent::Expression(expr) = star_exprs.unpack()
                {
                    return Some((
                        SimpleNameIterator::AnnotationName(name_d),
                        Some(annotation_),
                        expr,
                    ));
                }
                None
            }
            AssignmentContent::AugAssign(_, _, _) => None,
        }
    }

    pub fn maybe_simple_type_reassignment(&self) -> Option<NameOrPrimaryWithNames<'db>> {
        self.maybe_simple_targets_expression_assignment()
            .and_then(|(_, annot, expr)| match annot {
                None => expr.maybe_name_or_last_primary_name(),
                Some(_) => None,
            })
    }

    pub fn maybe_next_assignment(&self) -> Option<Self> {
        let stmt_ = self.node.parent_until(&[Nonterminal(stmt)])?;
        let next = stmt_.next_sibling()?;
        if !next.is_type(Nonterminal(stmt)) {
            return None;
        }
        let simple_stmts_ = next.nth_child(0);
        if !simple_stmts_.is_type(Nonterminal(simple_stmts)) {
            return None;
        }
        let simple_stmt_ = simple_stmts_.nth_child(0);
        if !simple_stmt_.is_type(Nonterminal(simple_stmt)) {
            return None;
        }
        let assignment_ = simple_stmt_.nth_child(0);
        if assignment_.is_type(Nonterminal(assignment)) {
            Some(Assignment::new(assignment_))
        } else {
            None
        }
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

pub enum SimpleNameIterator<'db> {
    AnnotationName(NameDef<'db>),
    Done,
    Targets(AssignmentTargetIterator<'db>),
}

impl<'db> Iterator for SimpleNameIterator<'db> {
    type Item = NameDef<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            SimpleNameIterator::AnnotationName(nd) => {
                let nd = *nd;
                *self = SimpleNameIterator::Done;
                Some(nd)
            }
            SimpleNameIterator::Targets(target_iterator) => {
                let Target::Name(name_d) = target_iterator.next()? else {
                    return None;
                };
                Some(name_d)
            }
            SimpleNameIterator::Done => None,
        }
    }
}

#[derive(Clone, Copy)]
pub enum AssignmentRightSide<'db> {
    YieldExpr(YieldExpr<'db>),
    StarExpressions(StarExpressions<'db>),
}

impl<'db> AssignmentRightSide<'db> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::YieldExpr(y) => y.index(),
            Self::StarExpressions(s) => s.index(),
        }
    }

    pub fn maybe_simple_expression(&self) -> Option<Expression<'db>> {
        match self {
            Self::YieldExpr(_) => None,
            Self::StarExpressions(star_exprs) => star_exprs.maybe_simple_expression(),
        }
    }

    pub fn is_literal_value(&self) -> bool {
        match self {
            Self::YieldExpr(_) => false,
            Self::StarExpressions(star_exprs) => match star_exprs.unpack() {
                StarExpressionContent::Expression(expr) => expr.is_literal_value(),
                _ => false,
            },
        }
    }

    pub fn is_inferrable_without_flow_analysis(&self) -> bool {
        match self {
            Self::StarExpressions(star_exprs) => {
                const SEARCH_NAMES: &[PyNodeType] =
                    &[Terminal(TerminalType::Name), Nonterminal(yield_expr)];
                star_exprs.node.search(SEARCH_NAMES, true).next().is_none()
            }
            Self::YieldExpr(_) => false,
        }
    }

    pub fn is_simple_assignment(&self, is_simple: &impl Fn(Expression) -> bool) -> bool {
        fn is_simple_expr(expr: Expression, is_simple: &impl Fn(Expression) -> bool) -> bool {
            if let Some(tup) = expr.maybe_tuple() {
                tup.iter().all(|s| match s {
                    StarLikeExpression::NamedExpression(ne) => {
                        is_simple_expr(ne.expression(), is_simple)
                    }
                    _ => false,
                })
            } else {
                is_simple(expr)
            }
        }
        match self {
            AssignmentRightSide::YieldExpr(_) => false,
            AssignmentRightSide::StarExpressions(s) => match s.unpack() {
                StarExpressionContent::Expression(expr) => is_simple_expr(expr, is_simple),
                StarExpressionContent::StarExpression(_) => false,
                StarExpressionContent::Tuple(star_exprs) => star_exprs.iter().all(|s| match s {
                    StarLikeExpression::Expression(expr) => is_simple_expr(expr, is_simple),
                    _ => false,
                }),
            },
        }
    }
}

pub struct StarTargetsIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for StarTargetsIterator<'db> {
    type Item = StarTargets<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.0.next()
            && node.is_type(Nonterminal(star_targets))
        {
            return Some(StarTargets::new(node));
        }
        None
    }
}

#[derive(Clone)]
pub struct AssignmentTargetIterator<'db>(StepBy<SiblingIterator<'db>>);

impl<'db> Iterator for AssignmentTargetIterator<'db> {
    type Item = Target<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(node) = self.0.next()
            && node.is_type(Nonterminal(star_targets))
        {
            return Some(Target::new(node));
        }
        None
    }
}

impl<'db> ImportFrom<'db> {
    pub fn level_with_dotted_name(&self) -> (usize, Option<DottedImportName<'db>>) {
        // | "from" ("." | "...")* dotted_import_name "import" import_from_targets
        // | "from" ("." | "...")+ "import" import_from_targets
        let mut level = 0;
        for node in self.node.iter_children().skip(1) {
            if node.is_type(Nonterminal(dotted_import_name)) {
                return (level, Some(DottedImportName::new(node)));
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

    pub fn insertion_point_for_new_name(&self, new_name: &str) -> InsertionPointForImportFrom {
        for node in self.node.iter_children().skip(3) {
            if node.is_type(Nonterminal(import_from_targets)) {
                let first = node.nth_child(0);
                if first.as_code() == "(" {
                    let second_last = node
                        .iter_children()
                        .fold((None, None), |(_, curr), next| (curr, Some(next)))
                        .0
                        .unwrap();
                    let mut insertion_code_index = second_last.end();
                    let mut addition = String::new();
                    if second_last.as_code() == "," {
                        if second_last.suffix().starts_with(" ") {
                            insertion_code_index += 1;
                        } else {
                            addition.push(' ');
                        }
                    } else {
                        addition += ", ";
                    }
                    addition += new_name;
                    return InsertionPointForImportFrom {
                        insertion_code_index,
                        addition,
                    };
                };
            }
        }
        InsertionPointForImportFrom {
            insertion_code_index: self.end(),
            addition: format!(", {new_name}"),
        }
    }
}

pub struct InsertionPointForImportFrom {
    pub insertion_code_index: CodeIndex,
    pub addition: String,
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
                // import_from_as_name: Name "as" name_def | name_def
                return Some(ImportFromAsName::new(child));
            }
        }
        None
    }
}

impl<'db> ImportFromAsName<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(name_def)) {
            NameDef::new(first)
        } else {
            NameDef::new(self.node.nth_child(2))
        }
    }

    pub fn unpack(&self) -> (Name<'db>, NameDef<'db>) {
        let first = self.node.nth_child(0);
        if first.is_type(Nonterminal(name_def)) {
            let name_d = NameDef::new(first);
            (name_d.name(), name_d)
        } else {
            // foo as bar
            debug_assert_eq!(first.type_(), Terminal(TerminalType::Name));
            let def = first.next_sibling().unwrap().next_sibling().unwrap();
            (Name::new(first), NameDef::new(def))
        }
    }

    fn is_stub_reexport(&self) -> bool {
        // foo as foo
        let (name, name_d) = self.unpack();
        // foo as bar is not a stub re-export
        name.index() != name_d.name_index() && name.as_code() == name_d.as_code()
    }

    pub fn import_from(&self) -> Option<ImportFrom<'db>> {
        self.node
            .parent_until(&[Nonterminal(import_from)])
            .map(ImportFrom::new)
    }
}

impl<'db> DottedImportName<'db> {
    pub fn unpack(&self) -> DottedImportNameContent<'db> {
        let mut children = self.node.iter_children();
        let first = children.next().unwrap();
        if first.is_type(Terminal(TerminalType::Name)) {
            DottedImportNameContent::Name(Name::new(first))
        } else {
            children.next();
            let name = children.next().unwrap();
            DottedImportNameContent::DottedName(DottedImportName::new(first), Name::new(name))
        }
    }
}

pub enum DottedImportNameContent<'db> {
    DottedName(DottedImportName<'db>, Name<'db>),
    Name(Name<'db>),
}

impl<'db> DottedPatternName<'db> {
    pub fn first_name(&self) -> Name<'db> {
        let n = self.node.next_leaf().unwrap();
        Name::new(n)
    }

    pub fn unpack(&self) -> DottedPatternNameContent<'db> {
        let mut children = self.node.iter_children();
        let first = children.next().unwrap();
        if first.is_type(Terminal(TerminalType::Name)) {
            DottedPatternNameContent::Name(Name::new(first))
        } else {
            children.next();
            let name = children.next().unwrap();
            DottedPatternNameContent::DottedName(DottedPatternName::new(first), Name::new(name))
        }
    }
}

pub enum DottedPatternNameContent<'db> {
    DottedName(DottedPatternName<'db>, Name<'db>),
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
    Simple(NameDef<'db>, Option<DottedImportName<'db>>),
    WithAs(DottedImportName<'db>, NameDef<'db>),
}

impl<'db> DottedAsName<'db> {
    #[inline]
    pub fn unpack(&self) -> DottedAsNameContent<'db> {
        let first = self.node.nth_child(0);
        let maybe_second = first.next_sibling();
        if first.is_type(Nonterminal(name_def)) {
            DottedAsNameContent::Simple(
                NameDef::new(first),
                maybe_second.map(|s| DottedImportName::new(s.next_sibling().unwrap())),
            )
        } else {
            DottedAsNameContent::WithAs(
                DottedImportName::new(first),
                NameDef::new(maybe_second.unwrap().next_sibling().unwrap()),
            )
        }
    }

    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(
            self.node
                .iter_children()
                .find(|n| n.is_type(Nonterminal(name_def)))
                .unwrap(),
        )
    }

    pub fn import(&self) -> ImportName<'db> {
        let n = self
            .node
            .parent_until(&[Nonterminal(import_name)])
            .expect("There should always be an import_name");
        ImportName::new(n)
    }
}

impl<'db> GlobalStmt<'db> {
    pub fn iter_name_defs(&self) -> impl Iterator<Item = NameDef<'db>> {
        self.node
            .iter_children()
            .skip(1)
            .step_by(2)
            .map(NameDef::new)
    }
}

impl<'db> AssertStmt<'db> {
    pub fn unpack(&self) -> (Expression<'db>, Option<Expression<'db>>) {
        let mut iterator = self.node.iter_children().skip(1);
        let first = iterator.next().unwrap();
        (Expression::new(first), iterator.nth(1).map(Expression::new))
    }
}

impl<'db> RaiseStmt<'db> {
    pub fn unpack(&self) -> Option<(Expression<'db>, Option<Expression<'db>>)> {
        let mut iterator = self.node.iter_children().skip(1);
        let first = iterator.next()?;
        Some((Expression::new(first), iterator.nth(1).map(Expression::new)))
    }
}

impl<'db> AwaitPrimary<'db> {
    pub fn primary(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.nth_child(1))
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
        if second.is_type(Nonterminal(name_def)) {
            PrimaryContent::Attribute(Name::new(second.nth_child(0)))
        } else if second.is_type(Terminal(TerminalType::Name)) {
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
        } else if second.is_type(Nonterminal(starred_expression)) {
            PrimaryContent::GetItem(SliceType::StarredExpression(StarredExpression::new(second)))
        } else {
            debug_assert_eq!(second.as_code(), ")");
            PrimaryContent::Execution(ArgumentsDetails::None)
        }
    }

    pub fn expect_closing_bracket_index(&self) -> NodeIndex {
        let last = self.node.iter_children().last().unwrap();
        debug_assert_eq!(last.as_code(), ")");
        last.index
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

    pub fn first_child_index(&self) -> NodeIndex {
        self.index() + 1
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
        } else if second.is_type(Nonterminal(starred_expression)) {
            PrimaryContent::GetItem(SliceType::StarredExpression(StarredExpression::new(second)))
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
        if parent.is_type(Nonterminal(primary)) {
            PrimaryParent::Primary(Primary::new(parent))
        } else {
            PrimaryParent::Other
        }
    }

    pub fn is_only_attributes(&self) -> bool {
        matches!(self.second(), PrimaryContent::Attribute(_))
            && match self.first() {
                PrimaryOrAtom::Atom(a) => matches!(a.unpack(), AtomContent::Name(_)),
                PrimaryOrAtom::Primary(p) => p.is_only_attributes(),
            }
    }

    pub fn expect_closing_bracket_index(&self) -> NodeIndex {
        let last = self.node.iter_children().last().unwrap();
        debug_assert_eq!(last.as_code(), ")");
        last.index
    }
}

pub enum PrimaryParent<'db> {
    Primary(Primary<'db>),
    Other,
}

impl<'db> BitwiseOr<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        Operation::new(self.node, "__or__", "__ror__", "|", true)
    }

    pub fn unpack(&self) -> (ExpressionPart<'db>, ExpressionPart<'db>) {
        // TODO this is probably unused
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();
        iter.next();
        let third = iter.next().unwrap();
        (ExpressionPart::new(first), ExpressionPart::new(third))
    }
}

impl<'db> BitwiseAnd<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        Operation::new(self.node, "__and__", "__rand__", "&", true)
    }
}

impl<'db> BitwiseXor<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        Operation::new(self.node, "__xor__", "__rxor__", "^", true)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct OpInfos {
    pub operand: &'static str,
    pub magic_method: &'static str,
    pub reverse_magic_method: &'static str,
    pub shortcut_when_same_type: bool,
}

#[derive(Copy, Clone)]
pub struct Operation<'db> {
    pub left: ExpressionPart<'db>,
    pub right: ExpressionPart<'db>,
    pub infos: OpInfos,
    pub index: NodeIndex,
}

impl<'db> Operation<'db> {
    fn new(
        node: PyNode<'db>,
        magic_method: &'static str,
        reverse_magic_method: &'static str,
        operand: &'static str,
        shortcut_when_same_type: bool,
    ) -> Self {
        let mut iter = node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        iter.next();
        let right = ExpressionPart::new(iter.next().unwrap());
        Self {
            left,
            infos: OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type,
            },
            right,
            index: node.index,
        }
    }
}

impl<'db> AugAssign<'db> {
    pub fn magic_methods(&self) -> (&'static str, OpInfos) {
        let code = self.node.as_code();
        let (inplace, magic_method, reverse_magic_method, operand) =
            match code.as_bytes().first().unwrap() {
                b'+' => ("__iadd__", "__add__", "__radd__", "+"),
                b'-' => ("__isub__", "__sub__", "__rsub__", "-"),
                b'*' => {
                    if code.as_bytes().get(1).unwrap() == &b'*' {
                        ("__ipow__", "__pow__", "__rpow__", "**")
                    } else {
                        ("__imul__", "__mul__", "__rmul__", "*")
                    }
                }
                b'/' => {
                    if code.as_bytes().get(1).unwrap() == &b'/' {
                        ("__ifloordiv__", "__floordiv__", "__rfloordiv__", "//")
                    } else {
                        ("__itruediv__", "__truediv__", "__rtruediv__", "/")
                    }
                }
                b'%' => ("__imod__", "__mod__", "__rmod__", "%"),
                b'&' => ("__iand__", "__and__", "__rand__", "&"),
                b'|' => ("__ior__", "__or__", "__ror__", "|"),
                b'^' => ("__ixor__", "__xor__", "__rxor__", "^"),
                b'<' => ("__ilshift__", "__lshift__", "__rlshift__", "<<"),
                b'>' => ("__irshift__", "__rshift__", "__rrshift__", ">>"),
                b'@' => ("__imatmul__", "__matmul__", "__rmatmul__", "@"),
                _ => unreachable!(),
            };
        (
            inplace,
            OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type: true,
            },
        )
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
            infos: OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type: true,
            },
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
            ("__mul__", "__rmul__", "*")
        } else if op == "/" {
            ("__truediv__", "__rtruediv__", "/")
        } else if op == "//" {
            ("__floordiv__", "__rfloordiv__", "//")
        } else if op == "%" {
            ("__mod__", "__rmod__", "%")
        } else {
            debug_assert_eq!(op, "@");
            ("__matmul__", "__rmatmul__", "@")
        };
        Operation {
            left,
            infos: OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type: true,
            },
            right,
            index: self.node.index,
        }
    }
}

impl<'db> ShiftExpr<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let op = iter.next().unwrap().as_code();
        let right = ExpressionPart::new(iter.next().unwrap());
        let (magic_method, reverse_magic_method, operand) = if op == ">>" {
            ("__rshift__", "__rrshift__", ">>")
        } else {
            debug_assert_eq!(op, "<<");
            ("__lshift__", "__rlshift__", "<<")
        };
        Operation {
            left,
            infos: OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type: true,
            },
            right,
            index: self.node.index,
        }
    }
}

impl<'db> Power<'db> {
    pub fn as_operation(&self) -> Operation<'db> {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        iter.next().unwrap();
        let right = ExpressionPart::new(iter.next().unwrap());
        Operation {
            left,
            infos: OpInfos {
                operand: "**",
                magic_method: "__pow__",
                reverse_magic_method: "__rpow__",
                shortcut_when_same_type: true,
            },
            right,
            index: self.node.index,
        }
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

impl<'db> Conjunction<'db> {
    pub fn unpack(&self) -> (ExpressionPart<'db>, ExpressionPart<'db>) {
        let mut iter = self.node.iter_children();
        let left = ExpressionPart::new(iter.next().unwrap());
        let _operand = iter.next().unwrap();
        (left, ExpressionPart::new(iter.next().unwrap()))
    }
}

impl<'db> Inversion<'db> {
    pub fn expression(&self) -> ExpressionPart<'db> {
        ExpressionPart::new(self.node.iter_children().nth(1).unwrap())
    }
}

impl<'db> Factor<'db> {
    pub fn unpack(&self) -> (Keyword<'db>, ExpressionPart<'db>) {
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();
        let second = iter.next().unwrap();
        (Keyword::new(first), ExpressionPart::new(second))
    }
}

#[derive(Copy, Clone)]
pub enum ComparisonContent<'db> {
    Equals(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    NotEquals(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    Is(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    IsNot(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    In(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    NotIn(ExpressionPart<'db>, Operand<'db>, ExpressionPart<'db>),
    Ordering(Operation<'db>),
}

impl<'db> ComparisonContent<'db> {
    pub fn left(&self) -> ExpressionPart<'db> {
        use ComparisonContent::*;
        match self {
            Equals(left, _, _)
            | NotEquals(left, _, _)
            | Is(left, _, _)
            | IsNot(left, _, _)
            | In(left, _, _)
            | NotIn(left, _, _) => *left,
            Ordering(operation) => operation.left,
        }
    }

    pub fn right(&self) -> ExpressionPart<'db> {
        use ComparisonContent::*;
        match self {
            Equals(_, _, right)
            | NotEquals(_, _, right)
            | Is(_, _, right)
            | IsNot(_, _, right)
            | In(_, _, right)
            | NotIn(_, _, right) => *right,
            Ordering(operation) => operation.right,
        }
    }
}

impl<'db> Comparisons<'db> {
    pub fn iter(&self) -> ComparisonIterator<'db> {
        let mut iterator = self.node.iter_children();
        ComparisonIterator {
            left: ExpressionPart::new(iterator.next().unwrap()),
            iterator,
        }
    }
}

pub struct ComparisonIterator<'db> {
    left: ExpressionPart<'db>,
    iterator: SiblingIterator<'db>,
}

impl<'db> Iterator for ComparisonIterator<'db> {
    type Item = ComparisonContent<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let op = self.iterator.next()?;
        let right = ExpressionPart::new(self.iterator.next().unwrap());
        let left = std::mem::replace(&mut self.left, right);
        let first_operand = op.nth_child(0);
        let (magic_method, reverse_magic_method, operand) = match first_operand.as_code() {
            "==" => return Some(ComparisonContent::Equals(left, Operand::new(op), right)),
            "!=" => return Some(ComparisonContent::NotEquals(left, Operand::new(op), right)),
            "is" => {
                if let Some(s) = first_operand.next_sibling() {
                    debug_assert_eq!(s.as_code(), "not");
                    return Some(ComparisonContent::IsNot(left, Operand::new(op), right));
                } else {
                    return Some(ComparisonContent::Is(left, Operand::new(op), right));
                }
            }
            "<" => ("__lt__", "__gt__", "<"),
            ">" => ("__gt__", "__lt__", ">"),
            "<=" => ("__le__", "__ge__", "<="),
            ">=" => ("__ge__", "__le__", ">="),
            "in" => return Some(ComparisonContent::In(left, Operand::new(op), right)),
            "not" => return Some(ComparisonContent::NotIn(left, Operand::new(op), right)),
            _ => unreachable!(),
        };
        Some(ComparisonContent::Ordering(Operation {
            left,
            infos: OpInfos {
                operand,
                magic_method,
                reverse_magic_method,
                shortcut_when_same_type: false,
            },
            right,
            index: op.index,
        }))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PrimaryOrAtom<'db> {
    Primary(Primary<'db>),
    Atom(Atom<'db>),
}

impl<'db> PrimaryOrAtom<'db> {
    pub fn as_code(&self) -> &'db str {
        match self {
            Self::Primary(p) => p.as_code(),
            Self::Atom(a) => a.as_code(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum PrimaryTargetOrAtom<'db> {
    PrimaryTarget(PrimaryTarget<'db>),
    Atom(Atom<'db>),
}

#[derive(Debug, Clone, Copy)]
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
    StarredExpression(StarredExpression<'db>),
}

impl<'db> SliceType<'db> {
    pub fn from_index(tree: &'db Tree, index: NodeIndex) -> Self {
        let node = tree.0.node_by_index(index);
        if node.is_type(Nonterminal(named_expression)) {
            SliceType::NamedExpression(NamedExpression::new(node))
        } else if node.is_type(Nonterminal(starred_expression)) {
            SliceType::StarredExpression(StarredExpression::new(node))
        } else if node.is_type(Nonterminal(slices)) {
            SliceType::Slices(Slices::new(node))
        } else {
            debug_assert_eq!(node.type_(), Nonterminal(slice));
            SliceType::Slice(Slice::new(node))
        }
    }

    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Slices(s) => s.index(),
            Self::Slice(s) => s.index(),
            Self::NamedExpression(n) => n.index(),
            Self::StarredExpression(s) => s.index(),
        }
    }

    pub fn last_leaf_index(&self) -> NodeIndex {
        let node = match self {
            SliceType::Slices(s) => s.node,
            SliceType::Slice(s) => s.node,
            SliceType::NamedExpression(n) => n.node,
            SliceType::StarredExpression(s) => s.node,
        };
        node.last_leaf_in_subtree().index
    }
}

impl<'db> Slices<'db> {
    pub fn iter(&self) -> SliceIterator<'db> {
        SliceIterator(self.node.iter_children())
    }
}

impl<'db> Slice<'db> {
    pub fn unpack(
        &self,
    ) -> (
        Option<Expression<'db>>,
        Option<Expression<'db>>,
        Option<Expression<'db>>,
    ) {
        let mut iterator = self.node.iter_children();
        let first = iterator
            .next()
            .filter(|y| y.is_type(Nonterminal(expression)));
        if first.is_some()
            && let Some(next) = iterator.next()
        {
            debug_assert_eq!(next.as_code(), ":");
        };
        let second = iterator
            .next()
            .filter(|y| y.is_type(Nonterminal(expression)));
        if second.is_some()
            && let Some(next) = iterator.next()
        {
            debug_assert_eq!(next.as_code(), ":");
        };
        let third = iterator.next();
        debug_assert!(iterator.next().is_none());
        (
            first.map(Expression::new),
            second.map(Expression::new),
            third.map(Expression::new),
        )
    }
}

#[derive(Clone, Copy)]
pub enum SliceContent<'db> {
    Slice(Slice<'db>),
    NamedExpression(NamedExpression<'db>),
    StarredExpression(StarredExpression<'db>),
}

#[derive(Clone)]
pub struct SliceIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for SliceIterator<'db> {
    type Item = SliceContent<'db>;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let result = self.0.next().map(|n| {
            if n.is_type(Nonterminal(slice)) {
                SliceContent::Slice(Slice::new(n))
            } else if n.is_type(Nonterminal(starred_expression)) {
                SliceContent::StarredExpression(StarredExpression::new(n))
            } else {
                SliceContent::NamedExpression(NamedExpression::new(n))
            }
        });
        self.0.next();
        result
    }
}

impl<'db> Arguments<'db> {
    pub fn iter(&self) -> ArgsIterator<'db> {
        ArgsIterator(self.node.iter_children())
    }

    pub fn search_names(&self) -> NameIterator<'db> {
        NameIterator(self.node.search(&[Terminal(TerminalType::Name)], false))
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

#[derive(Debug, Clone, Copy)]
pub struct ArgsIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for ArgsIterator<'db> {
    type Item = Argument<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for node in &mut self.0 {
            if node.is_type(Nonterminal(named_expression)) {
                return Some(Argument::Positional(NamedExpression::new(node)));
            } else if node.is_type(Nonterminal(kwargs)) {
                *self = Self(node.iter_children());
                return self.next();
            } else if node.is_type(Nonterminal(kwarg)) {
                return Some(Argument::Keyword(Kwarg::new(node)));
            } else if node.is_type(Nonterminal(starred_expression)) {
                return Some(Argument::Star(StarredExpression::new(node)));
            } else if node.is_type(Nonterminal(double_starred_expression)) {
                return Some(Argument::StarStar(StarStarExpression::new(node)));
            }
        }
        None
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Argument<'db> {
    Positional(NamedExpression<'db>),
    Keyword(Kwarg<'db>),
    Star(StarredExpression<'db>),
    StarStar(StarStarExpression<'db>),
}

impl Argument<'_> {
    pub fn index(&self) -> NodeIndex {
        match self {
            Self::Positional(n) => n.index(),
            Self::Keyword(k) => k.index(),
            Self::Star(s) => s.index(),
            Self::StarStar(d) => d.index(),
        }
    }
}

impl<'db> Kwarg<'db> {
    pub fn unpack(&self) -> (Name<'db>, Expression<'db>) {
        // kwarg: Name "=" expression
        let mut kwarg_iterator = self.node.iter_children();
        let name = kwarg_iterator.next().unwrap();
        kwarg_iterator.next();
        let arg = kwarg_iterator.next().unwrap();
        (Name::new(name), Expression::new(arg))
    }
}

impl<'db> StarredExpression<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> StarStarExpression<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> DelStmt<'db> {
    pub fn targets(&self) -> DelTargets<'db> {
        DelTargets::new(self.node.nth_child(1))
    }
}

pub enum DelTarget<'db> {
    Target(Target<'db>),
    DelTargets(DelTargets<'db>),
}

impl<'db> DelTargets<'db> {
    pub fn iter(&self) -> impl Iterator<Item = DelTarget<'db>> {
        self.node.iter_children().step_by(2).filter_map(|node| {
            if node.is_type(Nonterminal(del_t_atom)) {
                let targets = node.nth_child(1);
                // If it's not del_targets, it's a closing (and empty) `)` or `]`.
                targets
                    .is_type(Nonterminal(del_targets))
                    .then(|| DelTarget::DelTargets(DelTargets::new(targets)))
            } else {
                Some(DelTarget::Target(Target::new_non_iterator(node)))
            }
        })
    }
}

#[derive(Debug)]
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
    pub fn star_expressions(&self) -> Option<StarExpressions<'db>> {
        self.node
            .nth_child(0)
            .next_sibling()
            .map(StarExpressions::new)
    }
}

impl<'db> YieldExpr<'db> {
    pub fn unpack(&self) -> YieldExprContent<'db> {
        let Some(node) = self.node.iter_children().nth(1) else {
            return YieldExprContent::None;
        };
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
    None,
}

impl<'db> YieldFrom<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> TypeAlias<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        NameDef::new(self.node.nth_child(1))
    }

    pub fn unpack(&self) -> (NameDef<'db>, Option<TypeParams<'db>>, Expression<'db>) {
        let mut iterator = self.node.iter_children().skip(1);
        let name = NameDef::new(iterator.next().unwrap());
        let maybe_type_params = iterator.next().unwrap();
        let params = maybe_type_params
            .is_type(Nonterminal(type_params))
            .then(|| {
                // The node after type_params is an `=`
                iterator.next();
                TypeParams::new(maybe_type_params)
            });
        (name, params, Expression::new(iterator.next().unwrap()))
    }
}

impl<'db> TypeParams<'db> {
    pub fn iter(&self) -> impl Iterator<Item = TypeParam<'db>> {
        self.node
            .iter_children()
            .skip(1)
            .step_by(2)
            .filter_map(|child| {
                debug_assert!(matches!(
                    child.type_(),
                    Nonterminal(type_param) | PyNodeType::Keyword
                ));
                child
                    .is_type(Nonterminal(type_param))
                    .then(|| TypeParam::new(child))
            })
    }
}

pub enum TypeParamKind<'db> {
    TypeVar(Option<TypeParamBound<'db>>, Option<TypeParamDefault<'db>>),
    TypeVarTuple(Option<TypeParamStarredDefault<'db>>),
    ParamSpec(Option<TypeParamDefault<'db>>),
}

impl<'db> TypeParam<'db> {
    pub fn name_def(&self) -> NameDef<'db> {
        let mut n = self.node.nth_child(0);
        if n.is_leaf() {
            debug_assert!(matches!(n.as_code(), "*" | "**"));
            n = n.next_sibling().unwrap();
        }
        NameDef::new(n)
    }

    pub fn unpack(&self) -> (NameDef<'db>, TypeParamKind<'db>) {
        let mut iterator = self.node.iter_children();
        let first = iterator.next().unwrap();
        if first.is_type(Nonterminal(name_def)) {
            let mut bound = None;
            let mut default = None;
            let mut maybe_next = iterator.next();
            if let Some(next) = maybe_next
                && next.is_type(Nonterminal(type_param_bound))
            {
                bound = Some(TypeParamBound::new(next));
                maybe_next = iterator.next();
            }
            if let Some(next) = maybe_next
                && next.is_type(Nonterminal(type_param_default))
            {
                default = Some(TypeParamDefault::new(next));
            }
            debug_assert!(iterator.next().is_none());
            (NameDef::new(first), TypeParamKind::TypeVar(bound, default))
        } else if first.as_code() == "*" {
            let name_node = iterator.next().unwrap();
            let default = iterator.next().map(TypeParamStarredDefault::new);
            (
                NameDef::new(name_node),
                TypeParamKind::TypeVarTuple(default),
            )
        } else {
            debug_assert_eq!(first.as_code(), "**");
            let name_node = iterator.next().unwrap();
            let default = iterator.next().map(TypeParamDefault::new);
            (NameDef::new(name_node), TypeParamKind::ParamSpec(default))
        }
    }
}

impl<'db> TypeParamBound<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> TypeParamDefault<'db> {
    pub fn expression(&self) -> Expression<'db> {
        Expression::new(self.node.nth_child(1))
    }
}

impl<'db> TypeParamStarredDefault<'db> {
    pub fn unpack(&self) -> StarAnnotationContent<'db> {
        let n = self.node.nth_child(1);
        if n.is_type(Nonterminal(expression)) {
            StarAnnotationContent::Expression(Expression::new(n))
        } else {
            debug_assert_eq!(n.type_(), Nonterminal(star_expression));
            StarAnnotationContent::StarExpression(StarExpression::new(n))
        }
    }
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

    pub fn parent_scope(&self) -> Scope<'db> {
        scope_for_node(self.node)
    }
}

impl<'db> NameDef<'db> {
    #[inline]
    pub fn name(&self) -> Name<'db> {
        Name::new(self.node.nth_child(0))
    }

    pub fn name_index(&self) -> NodeIndex {
        debug_assert!(self.name().index() == self.index() + NAME_DEF_TO_NAME_DIFFERENCE);
        self.index() + NAME_DEF_TO_NAME_DIFFERENCE
    }

    pub fn parent(&self) -> NameDefParent {
        let parent = self.node.parent().unwrap();
        if parent.is_type(Nonterminal(t_primary)) {
            NameDefParent::Primary
        } else if parent.is_type(Nonterminal(global_stmt)) {
            NameDefParent::GlobalStmt
        } else if parent.is_type(Nonterminal(nonlocal_stmt)) {
            NameDefParent::NonlocalStmt
        } else {
            NameDefParent::Other
        }
    }

    pub fn maybe_assignment_definition(&self) -> Option<Assignment<'db>> {
        let node = self
            .node
            .parent_until(&[
                Nonterminal(assignment),
                Nonterminal(comprehension),
                Nonterminal(dict_comprehension),
                Nonterminal(lambda),
                Nonterminal(walrus),
                Nonterminal(stmt),
                ErrorNonterminal(stmt),
            ])
            .expect("There should always be a stmt");
        node.is_type(Nonterminal(assignment))
            .then(|| Assignment::new(node))
    }

    pub fn maybe_import(&self) -> Option<NameImportParent<'db>> {
        let node = self
            .node
            .parent_until(&[
                Nonterminal(stmt),
                Nonterminal(import_from_as_name),
                Nonterminal(dotted_as_name),
                ErrorNonterminal(stmt),
            ])
            .unwrap();
        if node.is_type(Nonterminal(stmt)) || node.is_type(ErrorNonterminal(stmt)) {
            None
        } else if node.is_type(Nonterminal(import_from_as_name)) {
            Some(NameImportParent::ImportFromAsName(ImportFromAsName::new(
                node,
            )))
        } else {
            debug_assert_eq!(node.type_(), Nonterminal(dotted_as_name));
            Some(NameImportParent::DottedAsName(DottedAsName::new(node)))
        }
    }

    pub fn expect_defining_stmt(&self) -> DefiningStmt<'db> {
        let stmt_node = self
            .node
            .parent_until(&[
                Nonterminal(function_def),
                Nonterminal(class_def),
                Nonterminal(assignment),
                Nonterminal(import_from_as_name),
                Nonterminal(import_name),
                Nonterminal(stmt),
                Nonterminal(lambda),
                Nonterminal(comprehension),
                Nonterminal(dict_comprehension),
                Nonterminal(walrus),
                Nonterminal(for_stmt),
                Nonterminal(try_stmt),
                Nonterminal(with_item),
                Nonterminal(del_stmt),
                Nonterminal(match_stmt),
                Nonterminal(type_alias),
                Nonterminal(global_stmt),
                Nonterminal(nonlocal_stmt),
                ErrorNonterminal(stmt),
            ])
            .expect("There should always be a stmt");
        if stmt_node.is_type(Nonterminal(function_def)) {
            DefiningStmt::FunctionDef(FunctionDef::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(class_def)) {
            DefiningStmt::ClassDef(ClassDef::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(assignment)) {
            DefiningStmt::Assignment(Assignment::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(import_from_as_name)) {
            DefiningStmt::ImportFromAsName(ImportFromAsName::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(import_name)) {
            DefiningStmt::ImportName(ImportName::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(lambda)) {
            DefiningStmt::Lambda(Lambda::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(comprehension)) {
            DefiningStmt::Comprehension(Comprehension::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(dict_comprehension)) {
            DefiningStmt::DictComprehension(DictComprehension::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(walrus)) {
            DefiningStmt::Walrus(Walrus::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(try_stmt)) {
            DefiningStmt::TryStmt(TryStmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(for_stmt)) {
            DefiningStmt::ForStmt(ForStmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(with_item)) {
            DefiningStmt::WithItem(WithItem::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(del_stmt)) {
            DefiningStmt::DelStmt(DelStmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(match_stmt)) {
            DefiningStmt::MatchStmt(MatchStmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(type_alias)) {
            DefiningStmt::TypeAlias(TypeAlias::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(global_stmt)) {
            DefiningStmt::GlobalStmt(GlobalStmt::new(stmt_node))
        } else if stmt_node.is_type(Nonterminal(nonlocal_stmt)) {
            DefiningStmt::NonlocalStmt(NonlocalStmt::new(stmt_node))
        } else if stmt_node.is_type(ErrorNonterminal(stmt)) {
            DefiningStmt::Error(Error::new(stmt_node))
        } else {
            unreachable!(
                "Reached a previously unknown defining statement {:?}",
                self.node
            )
        }
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
                Nonterminal(walrus),
                Nonterminal(type_alias),
                Nonterminal(type_param),
                Nonterminal(param_no_default),
                Nonterminal(param_with_default),
                Nonterminal(param_maybe_default),
                Nonterminal(starred_param),
                Nonterminal(double_starred_param),
                ErrorNonterminal(stmt),
            ])
            .expect("There should always be a stmt");
        if node.is_type(Nonterminal(class_def)) {
            TypeLike::ClassDef(ClassDef::new(node))
        } else if node.is_type(Nonterminal(assignment)) {
            TypeLike::Assignment(Assignment::new(node))
        } else if node.is_type(Nonterminal(function_def)) {
            TypeLike::Function(FunctionDef::new(node))
        } else if node.is_type(Nonterminal(stmt))
            | node.is_type(Nonterminal(walrus))
            | node.is_type(ErrorNonterminal(stmt))
        {
            TypeLike::Other
        } else if node.is_type(Nonterminal(import_from_as_name)) {
            TypeLike::ImportFromAsName(ImportFromAsName::new(node))
        } else if node.is_type(Nonterminal(dotted_as_name)) {
            TypeLike::DottedAsName(DottedAsName::new(node))
        } else if node.is_type(Nonterminal(type_alias)) {
            TypeLike::TypeAlias(TypeAlias::new(node))
        } else if node.is_type(Nonterminal(type_param)) {
            TypeLike::TypeParam(TypeParam::new(node))
        } else {
            debug_assert!(matches!(
                node.type_(),
                Nonterminal(param_no_default)
                    | Nonterminal(param_with_default)
                    | Nonterminal(param_maybe_default)
                    | Nonterminal(starred_param)
                    | Nonterminal(double_starred_param)
            ));
            TypeLike::ParamName(node.iter_children().nth(1).and_then(|n| {
                n.is_type(Nonterminal(annotation))
                    .then(|| Annotation::new(n))
            }))
        }
    }

    pub fn definition_range(&self) -> (NodeIndex, NodeIndex) {
        // Mostly used for LSP's targetRange in gotoDefinition, etc
        let mut parent = self.node.parent().unwrap();
        while matches!(
            parent.type_(),
            Nonterminal(
                star_targets
                    | star_target
                    | single_target
                    | import_from_as_name
                    | import_from_targets
                    | dotted_as_names
                    | dotted_as_name
            )
        ) {
            parent = parent.parent().unwrap();
        }
        (parent.start(), parent.end())
    }

    pub fn name_can_be_overwritten(&self) -> bool {
        let parent = self.node.parent().unwrap();
        // The following nodes can not be overwritten:
        // - Attributes with annotations
        // - Functions
        // - Classes
        // - Imports
        if matches!(
            parent.type_(),
            Nonterminal(function_def | class_def | import_from_as_name | dotted_as_name,)
        ) {
            return false;
        }
        let maybe_annotation = if parent.is_type(Nonterminal(single_target)) {
            parent.next_sibling()
        } else {
            parent.iter_children().nth(1)
        };
        !maybe_annotation.is_some_and(|n| n.is_type(Nonterminal(annotation)))
    }

    pub fn expect_class_def(&self) -> ClassDef<'db> {
        ClassDef::new(self.node.parent().unwrap())
    }

    pub fn maybe_name_of_func(&self) -> Option<FunctionDef<'db>> {
        let n = self.node.parent().unwrap();
        n.is_type(Nonterminal(function_def))
            .then(|| FunctionDef::new(n))
    }

    pub fn maybe_name_of_class(&self) -> Option<ClassDef<'db>> {
        let n = self.node.parent().unwrap();
        n.is_type(Nonterminal(class_def)).then(|| ClassDef::new(n))
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

    pub fn maybe_param_annotation(&self) -> Option<ParamAnnotation<'db>> {
        if let Some(next) = self.node.next_sibling() {
            if next.is_type(Nonterminal(annotation)) {
                return Some(ParamAnnotation::Annotation(Annotation::new(next)));
            } else if next.is_type(Nonterminal(star_annotation)) {
                return Some(ParamAnnotation::StarAnnotation(StarAnnotation::new(next)));
            }
        }
        None
    }

    pub fn maybe_parent_function_of_param(&self) -> Option<FunctionDef<'db>> {
        let parent = self.node.parent()?;
        if !matches!(
            parent.type_(),
            Nonterminal(param_no_default)
                | Nonterminal(param_with_default)
                | Nonterminal(param_maybe_default)
                | Nonterminal(starred_param)
                | Nonterminal(double_starred_param)
        ) {
            None
        } else {
            let par = parent.parent_until(&[Nonterminal(function_def)]).unwrap();
            Some(FunctionDef::new(par))
        }
    }

    pub fn func_param_including_error_recovery(&self) -> (NameDef<'db>, Option<Decorators<'db>>) {
        expect_func_parent_including_error_recovery(self.node)
    }
}

fn expect_func_parent_including_error_recovery(node: PyNode) -> (NameDef, Option<Decorators>) {
    let par = node
        .parent_until(&[Nonterminal(function_def), ErrorNonterminal(function_def)])
        .unwrap();
    let maybe_decorated = par.parent().unwrap();
    let dec = (maybe_decorated.is_type(Nonterminal(decorated))
        || maybe_decorated.is_type(ErrorNonterminal(decorated)))
    .then(|| Decorators::new(maybe_decorated.nth_child(0)));
    (NameDef::new(par.iter_children().nth(1).unwrap()), dec)
}

pub enum NameDefParent {
    Primary,
    GlobalStmt,
    NonlocalStmt,
    Other,
}

#[derive(Debug)]
pub enum NameImportParent<'db> {
    ImportFromAsName(ImportFromAsName<'db>),
    DottedAsName(DottedAsName<'db>),
}

impl NameImportParent<'_> {
    pub fn is_stub_reexport(&self) -> bool {
        match self {
            Self::ImportFromAsName(imp) => imp.is_stub_reexport(),
            Self::DottedAsName(dotted) => match dotted.unpack() {
                DottedAsNameContent::Simple(..) => false,
                DottedAsNameContent::WithAs(dotted, name_d) => dotted.as_code() == name_d.as_code(),
            },
        }
    }
}

pub enum UnpackedNumber<'db> {
    Int(Int<'db>),
    Float(Float<'db>),
    Complex(Complex<'db>),
}

impl<'db> UnpackedNumber<'db> {
    fn from_node(node: PyNode<'db>) -> Self {
        let code = node.as_code();
        if code.contains('j') || code.contains('J') {
            Self::Complex(Complex::new(node))
        } else if code.contains(['.', 'e', 'E'])
            && !code
                .strip_prefix('0')
                .is_some_and(|s| s.starts_with(['x', 'X']))
        {
            Self::Float(Float::new(node))
        } else {
            Self::Int(Int::new(node))
        }
    }
}

impl<'db> Atom<'db> {
    #[inline]
    pub fn unpack(&self) -> AtomContent<'db> {
        let mut iter = self.node.iter_children();
        let first = iter.next().unwrap();

        match first.type_() {
            Terminal(TerminalType::Name) => AtomContent::Name(Name::new(first)),
            Terminal(TerminalType::Number) => match UnpackedNumber::from_node(first) {
                UnpackedNumber::Int(int) => AtomContent::Int(int),
                UnpackedNumber::Float(float) => AtomContent::Float(float),
                UnpackedNumber::Complex(complex) => AtomContent::Complex(complex),
            },
            Nonterminal(strings) => AtomContent::Strings(Strings::new(first)),
            Nonterminal(bytes) => AtomContent::Bytes(Bytes::new(first)),
            PyNodeType::Keyword => match first.as_code() {
                "None" => AtomContent::NoneLiteral,
                "True" | "False" => AtomContent::Bool(Keyword::new(first)),
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

    pub fn maybe_expression_parent(&self) -> Option<Expression<'db>> {
        let n = self.node.parent().unwrap();
        n.is_type(Nonterminal(expression))
            .then(|| Expression::new(n))
    }

    pub fn is_literal_value(&self) -> bool {
        match self.unpack() {
            AtomContent::Float(_)
            | AtomContent::Int(_)
            | AtomContent::Complex(_)
            | AtomContent::Strings(_)
            | AtomContent::Bytes(_)
            | AtomContent::NoneLiteral
            | AtomContent::Bool(_) => true,
            AtomContent::NamedExpression(named_expr) => named_expr.expression().is_literal_value(),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub enum AtomContent<'db> {
    Name(Name<'db>),

    Float(Float<'db>),
    Int(Int<'db>),
    Complex(Complex<'db>),
    Strings(Strings<'db>),
    Bytes(Bytes<'db>),

    NoneLiteral,
    Bool(Keyword<'db>),
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

impl<'db> AtomContent<'db> {
    pub fn maybe_single_string_literal(&self) -> Option<StringLiteral<'db>> {
        match self {
            AtomContent::Strings(s) => s.maybe_single_string_literal(),
            _ => None,
        }
    }
}

impl<'db> Bytes<'db> {
    pub fn maybe_single_bytes_literal(&self) -> Option<BytesLiteral<'db>> {
        let mut iterator = self.node.iter_children();
        let first = iterator.next()?;
        iterator.next().is_none().then(|| BytesLiteral::new(first))
    }
}

impl<'db> BytesLiteral<'db> {
    pub fn content_as_bytes(&self) -> Cow<'db, [u8]> {
        parse_python_bytes_literal(self.node)
    }
}

impl<'db> StringLiteral<'db> {
    pub fn content(&self) -> &'db str {
        let code = self.node.as_code();
        let bytes_ = code.as_bytes();
        let mut start = 0;
        let mut quote = None;
        for (i, b) in bytes_.iter().enumerate() {
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
        let (start, end) = self.content_start_and_end_in_literal_internal();
        &code[start..end]
    }

    fn content_start_and_end_in_literal_internal(&self) -> (usize, usize) {
        let code = self.node.as_code();
        let bytes_ = code.as_bytes();
        let mut start = 0;
        let mut quote = None;
        for (i, b) in bytes_.iter().enumerate() {
            if *b == b'"' || *b == b'\'' {
                if let Some(quote) = quote {
                    if *b == quote && i == start + 3 {
                        return (start + 3, code.len() - 3);
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
        (start + 1, code.len() - 1)
    }

    pub fn content_start_and_end_in_literal(&self) -> (CodeIndex, CodeIndex) {
        let (start, end) = self.content_start_and_end_in_literal_internal();
        (start as CodeIndex, end as CodeIndex)
    }

    pub fn in_simple_assignment(&self) -> Option<NameDef<'db>> {
        in_simple_assignment(self.node)
    }

    pub fn as_python_string(&self) -> PythonString<'db> {
        PythonString::from_literal(self.node)
    }
}

fn in_simple_assignment(node: PyNode) -> Option<NameDef> {
    node.parent_until(&[Nonterminal(assignment), Nonterminal(stmt)])
        .and_then(|n| {
            if n.is_type(Nonterminal(stmt)) {
                return None;
            }
            Assignment::new(n).maybe_simple_type_expression_assignment()
        })
        .map(|(name, _, _)| name)
}

impl<'db> Strings<'db> {
    pub fn as_python_string(&self) -> PythonString<'db> {
        PythonString::new(self.node.iter_children())
    }

    pub fn iter(&self) -> StringIterator<'db> {
        StringIterator(self.node.iter_children())
    }

    pub fn maybe_single_string_literal(&self) -> Option<StringLiteral<'db>> {
        let mut iterator = self.iter();
        if let Some(StringType::String(s)) = iterator.next() {
            if iterator.next().is_some() {
                None
            } else {
                Some(s)
            }
        } else {
            None
        }
    }
}

pub struct StringIterator<'db>(SiblingIterator<'db>);

impl<'db> Iterator for StringIterator<'db> {
    type Item = StringType<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|n| {
            if n.is_type(Nonterminal(fstring)) {
                StringType::FString(FString::new(n))
            } else {
                StringType::String(StringLiteral::new(n))
            }
        })
    }
}

pub enum StringType<'db> {
    String(StringLiteral<'db>),
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
    pub fn unpack(&self) -> (Expressions<'db>, Option<FStringFormatSpec<'db>>) {
        let mut iterator = self.node.iter_children().skip(1);
        // This is actually an `expressions` node, but `star_expressions` is a super set.
        let exprs = Expressions::new(iterator.next().unwrap());
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

impl<'db> Expressions<'db> {
    pub fn iter(&self) -> impl Iterator<Item = Expression<'db>> {
        self.node.iter_children().step_by(2).map(Expression::new)
    }
}

#[derive(Debug, Clone)]
pub enum GotoNode<'db> {
    Name(Name<'db>),
    ImportFromAsName {
        import_as_name: ImportFromAsName<'db>,
        on_name: Name<'db>,
    },
    Primary(Primary<'db>),
    PrimaryTarget(PrimaryTarget<'db>),
    Operator {
        first: ExpressionPart<'db>,
        magic_method: &'static str,
        operator: Keyword<'db>,
    },
    AugAssignOperator {
        target: Target<'db>,
        inplace_magic_method: &'static str,
        normal_magic_method: &'static str,
        operator: Keyword<'db>,
    },
    GlobalName(NameDef<'db>),
    NonlocalName(NameDef<'db>),
    Atom(Atom<'db>),
    None,
}

impl<'db> GotoNode<'db> {
    pub fn on_name(&self) -> Option<Name<'db>> {
        Some(match self {
            GotoNode::Name(n) => *n,
            GotoNode::ImportFromAsName { on_name, .. } => *on_name,
            GotoNode::Primary(p) => match p.second() {
                PrimaryContent::Attribute(name) => name,
                _ => return None,
            },
            GotoNode::PrimaryTarget(primary_target) => match primary_target.second() {
                PrimaryContent::Attribute(name) => name,
                _ => return None,
            },
            GotoNode::GlobalName(n) | GotoNode::NonlocalName(n) => n.name(),
            GotoNode::Atom(_)
            | GotoNode::None
            | GotoNode::Operator { .. }
            | GotoNode::AugAssignOperator { .. } => return None,
        })
    }
}

#[derive(Debug, Clone)]
pub enum Target<'db> {
    Tuple(TargetIterator<'db>),
    Name(NameDef<'db>),
    NameExpression(PrimaryTarget<'db>, NameDef<'db>),
    IndexExpression(PrimaryTarget<'db>),
    Starred(StarTarget<'db>),
}

impl<'db> Target<'db> {
    fn new(node: PyNode<'db>) -> Self {
        // star_targets: ",".star_target+ [","]
        // star_target:? "*"? (t_primary | star_target_brackets | name_def)
        let mut iterator = node.iter_children();
        let first = iterator.next().unwrap();
        if iterator.next().is_none() {
            Self::new_non_iterator(first)
        } else {
            debug_assert!(matches!(
                node.type_(),
                Nonterminal(star_targets) | Nonterminal(del_targets)
            ));
            Self::Tuple(TargetIterator(node.iter_children().step_by(2)))
        }
    }

    fn new_non_iterator(node: PyNode<'db>) -> Self {
        if node.is_type(Nonterminal(name_def)) {
            Self::Name(NameDef::new(node))
        } else if node.is_type(Nonterminal(t_primary)) {
            Self::new_t_primary(node)
        } else if node.is_type(Nonterminal(star_target_brackets)) {
            let mut iterator = node.iter_children();
            let keyword = iterator.next().unwrap();
            let star_targets_ = iterator.next().unwrap();
            if keyword.as_code() == "(" {
                if star_targets_.is_leaf() {
                    debug_assert_eq!(star_targets_.as_code(), ")");
                    Self::Tuple(TargetIterator(
                        SiblingIterator::new_empty(&keyword).step_by(1),
                    ))
                } else {
                    Self::new(star_targets_)
                }
            } else {
                Self::Tuple(TargetIterator(star_targets_.iter_children().step_by(2)))
            }
        } else if node.is_type(Nonterminal(star_target)) {
            Self::Starred(StarTarget::new(node))
        } else {
            unreachable!("{:?}", node);
        }
    }

    fn new_t_primary(t_prim: PyNode<'db>) -> Self {
        t_prim
            .iter_children()
            .find(|x| x.is_type(Nonterminal(name_def)))
            .map(|name_d| Self::NameExpression(PrimaryTarget::new(t_prim), NameDef::new(name_d)))
            .unwrap_or_else(|| Self::IndexExpression(PrimaryTarget::new(t_prim)))
    }

    fn new_single_target(node: PyNode<'db>) -> Self {
        debug_assert_eq!(node.type_(), Nonterminal(single_target));

        // t_primary | name_def | "(" single_target ")"
        let first = node.nth_child(0);
        if first.is_type(Nonterminal(name_def)) {
            Self::Name(NameDef::new(first))
        } else if first.is_type(Nonterminal(t_primary)) {
            Self::new_t_primary(first)
        } else {
            debug_assert_eq!(node.nth_child(0).as_code(), "(");
            Self::new_single_target(node.nth_child(1))
        }
    }

    pub fn maybe_name_def(&self) -> Option<NameDef<'db>> {
        match self {
            Self::Name(name) => Some(*name),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Error<'db> {
    node: PyNode<'db>,
}

impl<'db> Error<'db> {
    #[inline]
    pub fn new(node: PyNode<'db>) -> Self {
        debug_assert!(node.is_error_recovery_node());
        Self { node }
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

    pub fn as_code(&self) -> &'db str {
        self.node.as_code()
    }

    pub fn is_dedent(&self) -> bool {
        // If we just have a single Error Dedent in an Error statement, it's a dedent that was not
        // properly used.
        self.node.maybe_error_node() == Some(stmt)
            && self.node.nth_child(0).maybe_error_leaf() == Some(TerminalType::Dedent)
    }

    pub fn iter_parts(&self) -> impl Iterator<Item = UnpackedError<'db>> {
        // Since error nodes are stmts,
        let first = self.node.nth_child(0);
        (!first.is_leaf())
            .then(|| {
                first.iter_children().filter_map(|n| {
                    Some(match n.type_() {
                        Nonterminal(block) => UnpackedError::Block(Block::new(n)),
                        Nonterminal(else_block) => UnpackedError::ElseBlock(ElseBlock::new(n)),
                        Nonterminal(except_block) => {
                            UnpackedError::ExceptBlock(ExceptBlock::new(n))
                        }
                        Nonterminal(except_star_block) => {
                            UnpackedError::ExceptStarBlock(ExceptStarBlock::new(n))
                        }
                        Nonterminal(case_block) => UnpackedError::CaseBlock(CaseBlock::new(n)),
                        Nonterminal(simple_stmt) => UnpackedError::SimpleStmt(SimpleStmt::new(n)),
                        Nonterminal(_) | ErrorNonterminal(_) => {
                            UnpackedError::NonBlockErrorPart(NonBlockErrorPart { node: n })
                        }
                        _ => {
                            return None;
                        }
                    })
                })
            })
            .into_iter()
            .flatten()
    }
}

impl<'db> SimpleStmt<'db> {
    pub fn contained_name_defs(&self) -> impl Iterator<Item = NameDef<'db>> {
        self.node
            .search(&[Nonterminal(name_def)], true)
            .map(|n| NameDef::new(n))
    }

    pub fn unpack(&self) -> SimpleStmtContent<'db> {
        let child = self.node.nth_child(0);
        if child.is_type(Nonterminal(assignment)) {
            SimpleStmtContent::Assignment(Assignment::new(child))
        } else if child.is_type(Nonterminal(import_from)) {
            SimpleStmtContent::ImportFrom(ImportFrom::new(child))
        } else if child.is_type(Nonterminal(import_name)) {
            SimpleStmtContent::ImportName(ImportName::new(child))
        } else if child.is_type(Nonterminal(type_alias)) {
            SimpleStmtContent::TypeAlias(TypeAlias::new(child))
        } else {
            SimpleStmtContent::Other
        }
    }
}

pub enum SimpleStmtContent<'db> {
    Assignment(Assignment<'db>),
    ImportFrom(ImportFrom<'db>),
    ImportName(ImportName<'db>),
    TypeAlias(TypeAlias<'db>),
    Other,
}

#[derive(Debug)]
pub struct NonBlockErrorPart<'db> {
    node: PyNode<'db>,
}

impl<'db> NonBlockErrorPart<'db> {
    pub fn contained_name_defs(&self) -> impl Iterator<Item = NameDef<'db>> {
        self.node
            .search(&[Nonterminal(name_def)], true)
            .map(|n| NameDef::new(n))
    }
}

create_interesting_node_searcher!(NonBlockErrorPart);

#[derive(Debug)]
pub enum UnpackedError<'db> {
    Block(Block<'db>),
    ElseBlock(ElseBlock<'db>),
    ExceptBlock(ExceptBlock<'db>),
    ExceptStarBlock(ExceptStarBlock<'db>),
    CaseBlock(CaseBlock<'db>),
    SimpleStmt(SimpleStmt<'db>),
    NonBlockErrorPart(NonBlockErrorPart<'db>),
}
