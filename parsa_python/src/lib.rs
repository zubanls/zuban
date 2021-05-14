#![recursion_limit = "1024"]
mod tokenizer;

pub use crate::tokenizer::PythonTerminalType;
use crate::tokenizer::{PythonTerminal, PythonTokenizer};
use parsa::{create_grammar, Grammar};

create_grammar!(
    static PYTHON_GRAMMAR, struct PythonGrammar, struct PythonTree, struct PythonNode,
    enum PythonNodeType, enum PythonNonterminalType, PythonTokenizer, PythonTerminal, PythonTerminalType,

    soft_keywords=[
        Name: "match" | "case" | "_"
    ]

    file: stmt* Endmarker

    decorator: "@" dotted_name [ "(" [arglist] ")" ] Newline
    decorators: decorator+
    decorated: decorators (class_def | function_def | async_function_def)

    async_function_def: "async" function_def
    function_def: "def" Name parameters ["->" test] ":" suite

    parameters: "(" [typedargslist] ")"
    param: Name "="  // TODO
    typedargslist: (
      (tfpdef ["=" test] ("," tfpdef ["=" test])* "," "/" ["," [ tfpdef ["=" test] (
            "," tfpdef ["=" test])* (["," [
            "*" [tfpdef] ("," tfpdef ["=" test])* ["," ["**" tfpdef [","]]]
          | "**" tfpdef [","]]])
      | "*" [tfpdef] ("," tfpdef ["=" test])* (["," ["**" tfpdef [","]]])
      | "**" tfpdef [","]]] )
    |  (tfpdef ["=" test] ("," tfpdef ["=" test])* ["," [
            "*" [tfpdef] ("," tfpdef ["=" test])* ["," ["**" tfpdef [","]]]
          | "**" tfpdef [","]]]
      | "*" [tfpdef] ("," tfpdef ["=" test])* ["," ["**" tfpdef [","]]]
      | "**" tfpdef [","])
    )
    tfpdef: Name [":" test]
    varargslist: vfpdef ["=" test ]("," vfpdef ["=" test])* "," "/" ["," [ (vfpdef ["=" test] ("," vfpdef ["=" test])* ["," [
            "*" [vfpdef] ("," vfpdef ["=" test])* ["," ["**" vfpdef [","]]]
          | "**" vfpdef [","]]]
      | "*" [vfpdef] ("," vfpdef ["=" test])* ["," ["**" vfpdef [","]]]
      | "**" vfpdef [","]) ]] | (vfpdef ["=" test] ("," vfpdef ["=" test])* ["," [
            "*" [vfpdef] ("," vfpdef ["=" test])* ["," ["**" vfpdef [","]]]
          | "**" vfpdef [","]]]
      | "*" [vfpdef] ("," vfpdef ["=" test])* ["," ["**" vfpdef [","]]]
      | "**" vfpdef [","]
    )
    vfpdef: Name

    stmt: @error_recovery simple_stmts | compound_stmt | Newline
    simple_stmts: simple_stmt (";" simple_stmt)* [";"] Newline
    simple_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
                 import_stmt | global_stmt | nonlocal_stmt | assert_stmt)
    expr_stmt: testlist_star_expr (annassign | augassign (yield_expr|testlist) |
                         ("=" (yield_expr|testlist_star_expr))*)
    annassign: ":" test ["=" (yield_expr|testlist_star_expr)]
    testlist_star_expr: (test|star_expr) ("," (test|star_expr))* [","]
    augassign: ("+=" | "-=" | "*=" | "@=" | "/=" | "%=" | "&=" | "|=" | "^=" |
                "<<=" | ">>=" | "**=" | "//=")
    // For normal and annotated assignments, additional restrictions enforced by the interpreter
    del_stmt: "del" exprlist
    pass_stmt: "pass"
    flow_stmt: break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
    break_stmt: "break"
    continue_stmt: "continue"
    return_stmt: "return" [testlist_star_expr]
    yield_stmt: yield_expr
    raise_stmt: "raise" [test ["from" test]]
    import_stmt:? import_name | import_from
    import_name: "import" dotted_as_names
    // note below: the ("." | "...") is necessary because "..." is tokenized as ELLIPSIS
    import_from: ("from" (("." | "...")* dotted_name | ("." | "...")+)
                  "import" ("*" | "(" import_as_names ")" | import_as_names))
    import_as_name: Name ["as" Name]
    dotted_as_name: dotted_name ["as" Name]
    import_as_names: ",".import_as_name+ ","?
    dotted_as_names: dotted_as_name ("," dotted_as_name)*
    dotted_name: Name ("." Name)*
    global_stmt: "global" Name ("," Name)*
    nonlocal_stmt: "nonlocal" Name ("," Name)*
    assert_stmt: "assert" test ["," test]

    compound_stmt:
        | if_stmt | while_stmt | for_stmt | try_stmt | with_stmt
        | function_def | class_def | decorated | async_stmt | match_stmt
    async_stmt: "async" (function_def | with_stmt | for_stmt)
    if_stmt: "if" namedexpr_test ":" suite ("elif" namedexpr_test ":" suite)* ["else" ":" suite]
    while_stmt: "while" namedexpr_test ":" suite ["else" ":" suite]
    for_stmt: "for" exprlist "in" testlist ":" suite ["else" ":" suite]
    try_stmt: ("try" ":" suite
               ((except_clause ":" suite)+
                ["else" ":" suite]
                ["finally" ":" suite] |
               "finally" ":" suite))
    with_stmt: "with" with_item ("," with_item)*  ":" suite
    with_item: test ["as" expr]
    // NB compile.c makes sure that the default except clause is last
    except_clause: "except" [test ["as" Name]]
    suite: simple_stmts | Newline Indent stmt+ Dedent

    match_stmt: "match" subject_expr ":" Newline Indent case_block+ Dedent
    subject_expr:
        | star_named_expression "," star_named_expressions?
        | named_expression
    case_block:
        | "case" patterns guard? ":" suite
    guard: "if" named_expression

    patterns:
        | open_sequence_pattern
        | pattern
    pattern:
        | as_pattern
        | or_pattern
    as_pattern:
        | or_pattern "as" capture_pattern
    or_pattern:
        | "|".closed_pattern+
    closed_pattern:
        | literal_pattern
        | wildcard_pattern
        | value_pattern
        | group_pattern
        | sequence_pattern
        | mapping_pattern
        | class_pattern
        | capture_pattern

    literal_pattern:
        | signed_number [("+" | "-") Number]
        | strings
        | "None"
        | "True"
        | "False"
    signed_number:
        | Number
        | "-" Number

    capture_pattern:
        | !"_" Name

    wildcard_pattern:
        | "_"

    value_pattern: Name "." ".".Name+

    group_pattern:
        | "(" pattern ")"

    sequence_pattern:
        | "[" maybe_sequence_pattern? "]"
        | "(" open_sequence_pattern? ")"
    open_sequence_pattern:
        | maybe_star_pattern "," maybe_sequence_pattern?
    maybe_sequence_pattern:
        | ",".maybe_star_pattern+ ","?
    maybe_star_pattern:
        | star_pattern
        | pattern
    star_pattern:
        | "*" (capture_pattern | wildcard_pattern)

    mapping_pattern:
        | "{" items_pattern? "}"
    items_pattern:
        | ",".key_value_pattern+ ","?
    key_value_pattern:
        | (literal_pattern | value_pattern) ":" pattern
        | double_star_pattern
    double_star_pattern:
        | "**" capture_pattern

    name_or_attr: ".".Name+
    class_pattern:
        | name_or_attr "(" ")"
        | name_or_attr "(" positional_patterns ","? ")"
        | name_or_attr "(" keyword_patterns ","? ")"
        | name_or_attr "(" positional_patterns "," keyword_patterns ","? ")"
    positional_patterns:
        | ",".pattern+
    keyword_patterns:
        | ",".keyword_pattern+
    keyword_pattern:
        | Name "=" pattern

    star_named_expressions: ",".star_named_expression+ [","]
    star_named_expression:
        | "*" disjunction
        | named_expression
    named_expression:
        | Name ":=" test
        | test

    namedexpr_test: Name ":=" test | test
    test: disjunction ["if" disjunction "else" test] | lambdef
    test_nocond: disjunction | lambdef_nocond
    lambdef: "lambda" [varargslist] ":" test
    lambdef_nocond: "lambda" [varargslist] ":" test_nocond
    disjunction:? conjunction ("or" conjunction)*
    conjunction:? not_test ("and" not_test)*
    not_test:? "not" not_test | comparison
    comparison:? expr (comp_op expr)*
    // <> isn"t actually a valid comparison operator in Python. It"s here for the
    // sake of a __future__ import described in PEP 401 (which really works :-)
    comp_op: "<"|">"|"=="|">="|"<="|"<>"|"!="|"in"|"not" "in"|"is"|"is" "not"
    star_expr: "*" expr
    expr: expr "|" xor_expr | xor_expr
    xor_expr:? and_expr ("^" and_expr)*
    and_expr:? [and_expr "&"] shift_expr
    shift_expr:? arith_expr (("<<"|">>") arith_expr)*
    arith_expr:? arith_expr ("+"|"-") term | term
    term:? [term ("*"|"@"|"/"|"%"|"//")] factor
    factor:? ("+"|"-"|"~") factor | power
    power:? atom_expr ["**" factor]
    atom_expr:? ["await"] atom trailer*
    atom:? ("(" [yield_expr|testlist_comp] ")" |
            "[" [testlist_comp] "]" |
            "{" [dictorsetmaker] "}" |
            Name | Number | strings | "..." | "None" | "True" | "False")
    testlist_comp: (namedexpr_test|star_expr) ( comp_for | ("," (namedexpr_test|star_expr))* [","] )
    trailer: "(" [arglist] ")" | "[" subscriptlist "]" | "." Name
    subscriptlist: subscript ("," subscript)* [","]
    subscript: test | [test] ":" [test] [sliceop]
    sliceop: ":" [test]
    exprlist: (expr|star_expr) ("," (expr|star_expr))* [","]
    testlist: test ("," test)* [","]
    dictorsetmaker: ( ((test ":" test | "**" expr)
                       (comp_for | ("," (test ":" test | "**" expr))* [","])) |
                      ((test | star_expr)
                       (comp_for | ("," (test | star_expr))* [","])) )

    class_def: "class" Name ["(" [arglist] ")"] ":" suite

    arglist: argument ("," argument)*  [","]

    // The reason that keywords are test nodes instead of Name is that using Name
    // results in an ambiguity. ast.c makes sure it"s a Name.
    // "test "=" test" is really "keyword "=" test", but we have no such token.
    // These need to be in a single rule to avoid grammar that is ambiguous
    // to our LL(1) parser. Even though "test" includes "*expr" in star_expr,
    // we explicitly match "*" here, too, to give it proper precedence.
    // Illegal combinations and orderings are blocked in ast.c:
    // multiple (test comp_for) arguments are blocked; keyword unpackings
    // that precede iterable unpackings are blocked; etc.
    argument: ( Name "=" test |
                test [comp_for] |
                test ":=" test |
                "**" test |
                "*" test )

    comp_iter: comp_for | comp_if
    sync_comp_for: "for" exprlist "in" disjunction [comp_iter]
    comp_for: ["async"] sync_comp_for
    comp_if: "if" test_nocond [comp_iter]

    // not used in grammar, but may appear in "node" passed from Parser to Compiler
    encoding_decl: Name

    yield_expr: "yield" [yield_arg]
    yield_arg: "from" test | testlist_star_expr

    strings: (String | fstring)+
    fstring: FStringStart fstring_content* FStringEnd
    fstring_content: FStringString | fstring_expr
    fstring_conversion: "!" Name
    fstring_expr: "{" testlist ["="] [ fstring_conversion ] [ fstring_format_spec ] "}"
    fstring_format_spec: ":" fstring_content*
);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_grammar() {
        let tree = PYTHON_GRAMMAR.parse("{foo: 1}\n".to_owned());
        let root_node = tree.get_root_node();
        assert_eq!(
            root_node.get_type(),
            PythonNodeType::Nonterminal(PythonNonterminalType::file)
        );
    }
}
