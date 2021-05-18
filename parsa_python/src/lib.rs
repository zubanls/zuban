// Heavily inspired by https://docs.python.org/3.10/reference/grammar.html
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

    decorator: "@" named_expression Newline
    decorators: decorator+
    decorated:? decorators (class_def | function_def | async_function_def)

    async_function_def: "async" function_def
    function_def: "def" Name parameters ["->" expression] ":" block

    parameters: "(" [typedargslist] ")"
    param: Name "="  // TODO
    typedargslist: (
      (tfpdef ["=" expression] ("," tfpdef ["=" expression])* "," "/" ["," [ tfpdef ["=" expression] (
            "," tfpdef ["=" expression])* (["," [
            "*" [tfpdef] ("," tfpdef ["=" expression])* ["," ["**" tfpdef [","]]]
          | "**" tfpdef [","]]])
      | "*" [tfpdef] ("," tfpdef ["=" expression])* (["," ["**" tfpdef [","]]])
      | "**" tfpdef [","]]] )
    |  (tfpdef ["=" expression] ("," tfpdef ["=" expression])* ["," [
            "*" [tfpdef] ("," tfpdef ["=" expression])* ["," ["**" tfpdef [","]]]
          | "**" tfpdef [","]]]
      | "*" [tfpdef] ("," tfpdef ["=" expression])* ["," ["**" tfpdef [","]]]
      | "**" tfpdef [","])
    )
    tfpdef: Name [":" expression]

    stmt: @error_recovery simple_stmts | compound_stmt | Newline
    simple_stmts: simple_stmt (";" simple_stmt)* [";"] Newline
    simple_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
                 import_stmt | global_stmt | nonlocal_stmt | assert_stmt)
    expr_stmt: star_expressions (annassign | augassign (yield_expr|expressions) |
                         ("=" (yield_expr|star_expressions))*)
    annassign: ":" expression ["=" (yield_expr|star_expressions)]
    star_expressions: (expression|star_expression) ("," (expression|star_expression))* [","]
    star_expression: "*" bitwise_or
    augassign: ("+=" | "-=" | "*=" | "@=" | "/=" | "%=" | "&=" | "|=" | "^=" |
                "<<=" | ">>=" | "**=" | "//=")
    // For normal and annotated assignments, additional restrictions enforced by the interpreter
    del_stmt: "del" exprlist
    pass_stmt: "pass"
    flow_stmt: break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
    break_stmt: "break"
    continue_stmt: "continue"
    return_stmt: "return" [star_expressions]
    yield_stmt: yield_expr
    raise_stmt: "raise" [expression ["from" expression]]
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
    assert_stmt: "assert" expression ["," expression]

    compound_stmt:
        | if_stmt | while_stmt | for_stmt | try_stmt | with_stmt
        | function_def | class_def | decorated | async_stmt | match_stmt
    async_stmt: "async" (function_def | with_stmt | for_stmt)
    if_stmt: "if" named_expression ":" block ("elif" named_expression ":" block)* ["else" ":" block]
    while_stmt: "while" named_expression ":" block ["else" ":" block]
    for_stmt: "for" exprlist "in" expressions ":" block ["else" ":" block]
    try_stmt: ("try" ":" block
               ((except_clause ":" block)+
                ["else" ":" block]
                ["finally" ":" block] |
               "finally" ":" block))
    with_stmt: "with" with_item ("," with_item)*  ":" block
    with_item: expression ["as" bitwise_or]
    // NB compile.c makes sure that the default except clause is last
    except_clause: "except" [expression ["as" Name]]
    block: simple_stmts | Newline Indent stmt+ Dedent

    match_stmt: "match" subject_expr ":" Newline Indent case_block+ Dedent
    subject_expr:
        | star_named_expression "," star_named_expressions?
        | named_expression
    case_block:
        | "case" patterns guard? ":" block
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

    lambda: "lambda" [lambda_parameters] ":" expression
    lambda_parameters:
        | lambda_param ("," lambda_param)* "," "/" [
                "," [
                    lambda_param ("," lambda_param)* [
                        "," [
                            "*" [Name] ("," lambda_param)* ["," [lambda_double_starred_param [","]]]
                            | lambda_double_starred_param [","]
                        ]
                    ]
                    | "*" [Name] ("," lambda_param)* ["," [lambda_double_starred_param [","]]]
                    | lambda_double_starred_param [","]
                ]
            ]
        | (
                    lambda_param ("," lambda_param)* [
                        "," [
                            "*" [Name] ("," lambda_param)* ["," [lambda_double_starred_param [","]]]
                            | lambda_double_starred_param [","]
                        ]
                    ]
                    | "*" [Name] ("," lambda_param)* ["," [lambda_double_starred_param [","]]]
                    | lambda_double_starred_param [","]
        )
    lambda_param: Name ["=" expression ]
    lambda_double_starred_param: "**" Name

    star_named_expressions: ",".star_named_expression+ [","]
    star_named_expression: "*" disjunction | named_expression
    named_expression: Name ":=" expression | expression

    expressions: expression ("," expression)* [","]
    expression: disjunction ["if" disjunction "else" expression] | lambda
    disjunction:? conjunction ("or" conjunction)*
    conjunction:? inversion ("and" inversion)*
    inversion:? "not" inversion | comparison
    comparison:? bitwise_or (comp_op bitwise_or)*
    // <> isn"t actually a valid comparison operator in Python. It"s here for the
    // sake of a __future__ import described in PEP 401 (which really works :-)
    comp_op: "<"|">"|"=="|">="|"<="|"<>"|"!="|"in"|"not" "in"|"is"|"is" "not"
    bitwise_or:   [bitwise_or "|"] bitwise_xor
    bitwise_xor:? [bitwise_xor "^"] bitwise_and
    bitwise_and:? [bitwise_and "&"] shift_expr
    shift_expr:?  [shift_expr ("<<"|">>")] sum
    sum:? sum ("+"|"-") term | term
    term:? [term ("*"|"@"|"/"|"%"|"//")] factor
    factor:? ("+"|"-"|"~") factor | power
    power:? await_primary ["**" factor]
    await_primary:? ["await"] primary
    primary:?
          primary "." Name
        | primary "(" [arguments] ")"
        | primary "[" slices "]"
        | atom
    atom:?
          "(" [tuple_content | yield_expr | named_expression | comprehension] ")"
        | "[" [star_named_expressions | comprehension] "]"
        | "{" [dict_content | star_named_expressions | dict_comprehension | comprehension] "}"
        | Name | Number | strings | "..." | "None" | "True" | "False"
    slices: ",".slice+ [","]
    slice: named_expression | expression? ":" expression? [":" expression?]
    exprlist: (bitwise_or|star_expression) ("," (bitwise_or|star_expression))* [","]

    class_def: "class" Name ["(" [arguments] ")"] ":" block

    comprehension: named_expression for_if_clauses
    for_if_clauses: async_for_if_clause+
    async_for_if_clause:? ["async"] sync_for_if_clause
    sync_for_if_clause: "for" exprlist "in" disjunction comp_if*
    comp_if: "if" disjunction

    dict_comprehension: dict_key_value for_if_clauses
    dict_content: ",".(dict_starred | dict_key_value)+ [","]
    dict_starred: "**" bitwise_or
    dict_key_value: expression ":" expression

    tuple_content: star_named_expression "," [star_named_expressions]

    yield_expr: "yield" [yield_from | star_expressions]
    yield_from: "from" expression

    arguments:
        | ",".(starred_expression | named_expression !"=")+ ["," kwargs?]
        | kwargs
    kwargs:
        | ",".(kwarg | starred_expression)+ ","?
        | ",".(kwarg | starred_expression)+ "," ",".(kwarg | double_starred_expression)+ ","?
        | ",".(kwarg | double_starred_expression)+ ","?
    kwarg: Name "=" expression
    starred_expression: "*" expression
    double_starred_expression: "**" expression

    strings: (String | fstring)+
    fstring: FStringStart fstring_content* FStringEnd
    fstring_content: FStringString | fstring_expr
    fstring_conversion: "!" Name
    fstring_expr: "{" expressions ["="] [ fstring_conversion ] [ fstring_format_spec ] "}"
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
