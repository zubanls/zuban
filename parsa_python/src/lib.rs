// Heavily inspired by https://docs.python.org/3.10/reference/grammar.html
#![recursion_limit = "2048"]
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

    stmt: @error_recovery simple_stmts | compound_stmt | Newline
    simple_stmts: simple_stmt (";" simple_stmt)* [";"] Newline
    // NOTE: assignment MUST precede expression, otherwise parsing a simple assignment
    // will throw a SyntaxError.
    simple_stmt:
        | assignment | star_expressions | del_stmt | pass_stmt
        | import_name | import_from | global_stmt | nonlocal_stmt | assert_stmt
        | break_stmt | continue_stmt | return_stmt | raise_stmt | yield_stmt
    assignment:
        | (star_targets "=" )+ (yield_expr | star_expressions)
        | single_target ":" expression ["=" (yield_expr | star_expressions)]
        | single_target augassign (yield_expr | star_expressions)

    augassign: ("+=" | "-=" | "*=" | "@=" | "/=" | "%=" | "&=" | "|=" | "^=" |
                "<<=" | ">>=" | "**=" | "//=")
    del_stmt: "del" targets
    pass_stmt: "pass"
    break_stmt: "break"
    continue_stmt: "continue"
    return_stmt: "return" [star_expressions]
    yield_stmt: yield_expr
    raise_stmt: "raise" [expression ["from" expression]]
    global_stmt: "global" ",".name_definition+
    nonlocal_stmt: "nonlocal" ",".name_definition+
    assert_stmt: "assert" expression ["," expression]

    import_name: "import" dotted_as_names
    // note below: the ("." | "...") is necessary because "..." is tokenized as ELLIPSIS
    import_from:
        | "from" ("." | "...")* dotted_name "import" import_from_targets
        | "from" ("." | "...")+ "import" import_from_targets
    dotted_as_names: ",".dotted_as_name+
    dotted_as_name: dotted_name ["as" Name]
    dotted_name: [dotted_name "."] Name
    import_from_targets: "*" | "(" ",".import_from_as_name+ ","? ")" | ",".import_from_as_name+
    import_from_as_name: Name ["as" Name]

    compound_stmt:
        | if_stmt | while_stmt | for_stmt | try_stmt | with_stmt
        | function_def | class_def | decorated | async_stmt | match_stmt
    async_stmt: "async" (function_def | with_stmt | for_stmt)
    if_stmt: "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?
    else_block: "else" ":" block
    while_stmt: "while" named_expression ":" block else_block?
    for_stmt: "for" star_targets "in" star_expressions ":" block else_block?
    try_stmt: "try" ":" block (except_block+ else_block? finally_block | finally_block)
    except_block: except_clause ":" block
    except_clause: "except" [expression ["as" name_definition]]
    finally_block: "finally" ":" block
    with_stmt: "with" ("(" ",".with_item+ ","? ")" | ",".with_item+ )  ":" block
    with_item: expression ["as" star_target]

    match_stmt: "match" subject_expr ":" Newline Indent case_block+ Dedent
    subject_expr:
        | star_named_expression "," star_named_expressions?
        | named_expression
    case_block: "case" patterns guard? ":" block
    guard: "if" named_expression

    patterns: open_sequence_pattern | pattern
    pattern: as_pattern | or_pattern
    as_pattern: or_pattern "as" pattern_capture_target
    or_pattern: "|".closed_pattern+
    closed_pattern:
        | literal_pattern | wildcard_pattern | pattern_capture_target | value_pattern
        | group_pattern | sequence_pattern | mapping_pattern | class_pattern

    literal_pattern:
        | complex_number | signed_number | strings
        | "None" | "True" | "False"
    complex_number: signed_number ("+"|"-") Number
    signed_number: "-"? Number

    pattern_capture_target: !"_" name_definition
    wildcard_pattern: "_"
    value_pattern: dotted_name

    group_pattern: "(" pattern ")"
    sequence_pattern:
        | "[" maybe_sequence_pattern? "]"
        | "(" open_sequence_pattern? ")"
    open_sequence_pattern: maybe_star_pattern "," maybe_sequence_pattern?
    maybe_sequence_pattern: ",".maybe_star_pattern+ ","?
    maybe_star_pattern: star_pattern | pattern
    star_pattern: "*" (pattern_capture_target | wildcard_pattern)

    mapping_pattern:
        | "{" double_star_pattern? "}"
        | "{" ",".key_value_pattern+ ["," double_star_pattern?] "}"
    key_value_pattern: (literal_pattern | value_pattern) ":" pattern
    double_star_pattern: "**" pattern_capture_target ","?

    class_pattern:
        | dotted_name "(" ")"
        | dotted_name "(" positional_patterns ","? ")"
        | dotted_name "(" keyword_patterns ","? ")"
        | dotted_name "(" positional_patterns "," keyword_patterns ","? ")"
    positional_patterns: ",".pattern+
    keyword_patterns: ",".keyword_pattern+
    keyword_pattern: Name "=" pattern

    async_function_def: "async" function_def
    function_def: "def" name_definition "(" [parameters] ")" ["->" expression] ":" block

    decorator: "@" named_expression Newline
    decorators: decorator+
    decorated:? decorators (class_def | function_def | async_function_def)

    class_def: "class" name_definition ["(" [arguments] ")"] ":" block

    block: simple_stmts | Newline Indent stmt+ Dedent

    star_expressions: ",".(expression|star_expression)+ [","]
    star_expression: "*" bitwise_or
    star_named_expressions: ",".star_named_expression+ [","]
    star_named_expression: "*" disjunction | named_expression

    named_expression: name_definition ":=" expression | expression

    expressions: ",".expression+ [","]
    expression: disjunction ["if" disjunction "else" expression] | lambda

    lambda: "lambda" [lambda_parameters] ":" expression

    parameters: 
        // no-default
        | ",".param_no_default+ ["," [star_etc]]
        // no-default slash no-default default
        | ",".param_no_default+ "," "/" ["," [
                ",".param_no_default+ [
                    "," [
                             ",".param_with_default+ ["," [star_etc]]
                             | [star_etc]
                        ]]
                | star_etc
            ]]
        // no-default slash default
        | ",".param_no_default+ "," "/" ["," [
                ",".param_with_default+ ["," [star_etc]]
                | star_etc
            ]]
        // no-default default
        | ",".param_no_default+ "," ",".param_with_default+ (
            ["," [star_etc]]
            // no-default default slash default
            | "," "/" ["," [
                ",".param_with_default+ ["," [star_etc]]
                | star_etc
            ]]
        )
        // default slash default
        | ",".param_with_default+ "," "/" ["," [
                ",".param_with_default+ ["," [star_etc]]
                | star_etc
            ]]
        // default
        | ",".param_with_default+ ["," [star_etc]]
        // just star args
        | star_etc
    star_etc:
        | "*" starred_param ["," ",".param+] ["," [double_starred_param ","?]]
        | "*" "," ",".param+ ["," [double_starred_param ","?]]
        | double_starred_param [","]
    param_no_default: Name annotation? !"="
    param_with_default: Name annotation? "=" expression
    param: Name annotation? ["=" expression ]
    starred_param: Name annotation?
    double_starred_param: "**" Name annotation?
    annotation: ":" expression

    // Lambda params is basically a repetition of normal params without annotations
    lambda_parameters:
        // no-default
        | ",".lambda_param_no_default+ ["," [lambda_star_etc]]
        // no-default slash no-default default
        | ",".lambda_param_no_default+ "," "/" ["," [
                ",".lambda_param_no_default+ [
                    "," [
                             ",".lambda_param_with_default+ ["," [lambda_star_etc]]
                             | [lambda_star_etc]
                        ]]
                | lambda_star_etc
            ]]
        // no-default slash default
        | ",".lambda_param_no_default+ "," "/" ["," [
                ",".lambda_param_with_default+ ["," [lambda_star_etc]]
                | lambda_star_etc
            ]]
        // no-default default
        | ",".lambda_param_no_default+ "," ",".lambda_param_with_default+ (
            ["," [lambda_star_etc]]
            // no-default default slash default
            | "," "/" ["," [
                ",".lambda_param_with_default+ ["," [lambda_star_etc]]
                | lambda_star_etc
            ]]
        )
        // default slash default
        | ",".lambda_param_with_default+ "," "/" ["," [
                ",".lambda_param_with_default+ ["," [lambda_star_etc]]
                | lambda_star_etc
            ]]
        // default
        | ",".lambda_param_with_default+ ["," [lambda_star_etc]]
        // just star args
        | lambda_star_etc
    lambda_star_etc:
        | "*" lambda_starred_param ["," ",".lambda_param+] ["," [lambda_double_starred_param ","?]]
        | "*" "," ",".lambda_param+ ["," [lambda_double_starred_param ","?]]
        | lambda_double_starred_param [","]
    lambda_param_no_default: Name !"="
    lambda_param_with_default: Name "=" expression
    lambda_param: Name ["=" expression ]
    lambda_starred_param: Name
    lambda_double_starred_param: "**" Name

    disjunction:? [disjunction "or"] conjunction
    conjunction:? [conjunction "and"] inversion
    inversion:? "not" inversion | comparison
    comparison:? [comparison comp_op] bitwise_or
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
        | primary "(" [arguments | comprehension] ")"
        | primary "[" slices "]"
        | atom
    atom:?
          "(" [tuple_content | yield_expr | named_expression | comprehension] ")"
        | "[" [star_named_expressions | comprehension] "]"
        | "{" [dict_content | star_named_expressions | dict_comprehension | comprehension] "}"
        | Name | Number | strings | "..." | "None" | "True" | "False"
    slices: ",".slice+ [","]
    slice: expression? ":" expression? [":" expression?] | named_expression

    comprehension: named_expression for_if_clauses
    for_if_clauses: async_for_if_clause+
    async_for_if_clause:? ["async"] sync_for_if_clause
    sync_for_if_clause: "for" star_targets "in" disjunction comp_if*
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

    star_targets: ",".star_target+ [","]
    star_target: "*"? target_with_star_atom
    target_with_star_atom: t_primary | star_atom
    star_atom:
        | name_definition
        | "(" [star_targets] ")"
        | "[" [star_targets] "]"

    single_target: t_primary | name_definition | "(" single_target ")"

    targets: ",".target+ [","]
    target: t_primary | t_atom
    t_primary:
        | (
              t_primary "." Name
            | t_primary "(" [arguments|comprehension] ")"
            | atom
        ) &("."|"["|"(")
        | t_primary "[" slices "]"
        | t_primary "." name_definition
    t_atom: name_definition | "(" [targets] ")" | "[" [targets] "]"
    name_definition: Name

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
