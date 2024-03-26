// Heavily inspired by https://docs.python.org/3.10/reference/grammar.html
// and adapted to Python 3.13

#![recursion_limit = "2048"]
mod tokenizer;

use parsa::{create_grammar, Grammar};
pub use parsa::{CodeIndex, NodeIndex};

pub use crate::tokenizer::TerminalType;
use crate::tokenizer::{PyTerminal, PythonTokenizer};

create_grammar!(
    static PYTHON_GRAMMAR, struct PythonGrammar, struct PyTree, struct PyNode,
    enum PyNodeType, enum NonterminalType, PythonTokenizer, PyTerminal, TerminalType,

    soft_keywords=[
        Name: "match" | "case" | "_"
    ]

    // STARTING RULES
    // ==============
    file: stmt* Endmarker

    // GENERAL STATEMENTS
    // ==================
    stmt: @error_recovery
          simple_stmts | Newline
        | if_stmt | while_stmt | for_stmt | try_stmt | with_stmt
        | function_def | class_def | decorated | async_stmt | match_stmt
    simple_stmts: simple_stmt (";" simple_stmt)* [";"] Newline
    // NOTE: assignment MUST precede expression, otherwise parsing a simple assignment
    // will throw a SyntaxError.
    simple_stmt:
        | assignment | star_expressions | del_stmt | pass_stmt
        | import_name | import_from | global_stmt | nonlocal_stmt | assert_stmt
        | break_stmt | continue_stmt | return_stmt | raise_stmt | yield_expr
    async_stmt: "async" (function_def | with_stmt | for_stmt)

    // SIMPLE STATEMENTS
    // =================
    assignment:
        | (star_targets "=" )+ (yield_expr | star_expressions)
        | single_target annotation ["=" (yield_expr | star_expressions)]
        | single_target augassign (yield_expr | star_expressions)

    augassign: ("+=" | "-=" | "*=" | "@=" | "/=" | "%=" | "&=" | "|=" | "^=" |
                "<<=" | ">>=" | "**=" | "//=")
    return_stmt: "return" [star_expressions]
    raise_stmt: "raise" [expression ["from" expression]]
    global_stmt: "global" ",".Name+
    nonlocal_stmt: "nonlocal" ",".Name+
    del_stmt: "del" del_targets
    assert_stmt: "assert" expression ["," expression]
    pass_stmt: "pass"
    break_stmt: "break"
    continue_stmt: "continue"

    // Import statements
    // -----------------
    import_name: "import" dotted_as_names
    // note below: the ("." | "...") is necessary because "..." is tokenized as ELLIPSIS
    import_from:
        | "from" ("." | "...")* dotted_name "import" import_from_targets
        | "from" ("." | "...")+ "import" import_from_targets
    import_from_targets: "*" | "(" ",".import_from_as_name+ ","? ")" | ",".import_from_as_name+
    import_from_as_name: Name "as" name_definition | name_definition
    dotted_as_names: ",".dotted_as_name+
    dotted_as_name: dotted_name "as" name_definition | name_definition ["." dotted_name]
    dotted_name: [dotted_name "."] Name

    // COMPOUND STATEMENTS
    // ===================

    // Common elements
    // ---------------

    block: simple_stmts | Newline Indent stmt+ Dedent
    decorators: decorator+
    decorator: "@" named_expression Newline
    decorated: decorators (class_def | function_def | async_function_def)

    // Class definitions
    // -----------------

    class_def: "class" name_definition ["(" [arguments] ")"] ":" block

    // Function definitions
    // --------------------

    async_function_def: "async" function_def
    function_def: "def" name_definition function_def_parameters return_annotation? ":" block
    return_annotation: "->" expression

    // Function parameters
    // -------------------

    function_def_parameters: "(" [parameters] ")"

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
        | starred_param ["," ",".param_maybe_default+] ["," [double_starred_param ","?]]
        | "*" "," ",".param_maybe_default+ ["," [double_starred_param ","?]]
        | double_starred_param [","]
    param_no_default: name_definition annotation? !"="
    param_with_default: name_definition annotation? "=" expression
    param_maybe_default: name_definition annotation? ["=" expression ]
    starred_param: "*" name_definition star_annotation?
    double_starred_param: "**" name_definition annotation?
    annotation: ":" expression
    star_annotation: ":" (star_expression | expression)

    // If statement
    // ------------

    if_stmt: "if" named_expression ":" block ("elif" named_expression ":" block)* else_block?
    else_block: "else" ":" block

    // While statement
    // ---------------

    while_stmt: "while" named_expression ":" block else_block?

    // For statement
    // -------------

    for_stmt: "for" star_targets "in" star_expressions ":" block else_block?

    // With statement
    // --------------

    with_stmt: "with" with_items ":" block
    with_items: "(" ",".with_item+ ","? ")" | ",".with_item+
    with_item: expression ["as" star_target]

    // Try statement
    // -------------

    try_stmt: "try" ":" block ((except_block+ | except_star_block+) else_block? finally_block? | finally_block)

    // Except statement
    // ----------------

    except_block: "except" [except_expression] ":" block
    except_star_block: "except" "*" except_expression ":" block
    except_expression: expression ["as" name_definition]
    finally_block: "finally" ":" block

    // Match statement
    // ---------------

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
        | literal_pattern | class_pattern | wildcard_pattern
        | group_pattern | sequence_pattern | mapping_pattern
        | pattern_capture_target | value_pattern

    literal_pattern:
        | complex_number | signed_number | strings | bytes
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
        | dotted_name "(" param_patterns ","? ")"
    param_patterns:
        | ",".(pattern !"=")+ [",".(keyword_pattern)+]
        | ",".(keyword_pattern)+
    keyword_pattern: Name "=" pattern

    // Type statement
    // ---------------
    //type_alias: "type" Name [type_params] "=" expression


    // Type parameter declaration
    // --------------------------
    /*
    type_params: "[" type_param_seq  "]"

    type_param_seq: ",".type_param+ [","]

    type_param:
        | Name [type_param_bound]
        | "*" Name ":" expression
        | "*" Name
        | "**" Name ":" expression
        | "**" Name

    type_param_bound: ":" expression
    */

    // EXPRESSIONS
    // -----------

    expressions: ",".expression+ [","]
    expression: ternary | lambda
    ternary:? disjunction ["if" disjunction "else" expression]

    yield_expr: "yield" [yield_from | star_expressions]
    yield_from: "from" expression

    star_expressions: ",".(expression|star_expression)+ [","]
    star_expression: "*" bitwise_or
    star_named_expressions: ",".star_named_expression+ [","]
    star_named_expression:? "*" disjunction | named_expression

    named_expression: name_definition ":=" expression | expression

    disjunction:? [disjunction "or"] conjunction
    conjunction:? [conjunction "and"] inversion
    inversion:? "not" inversion | comparison

    // Comparison operators
    // --------------------

    comparison:? bitwise_or (comp_op bitwise_or)*
    comp_op: "<"|">"|"=="|">="|"<="|"!="|"in"|"not" "in"|"is"|"is" "not"

    // Bitwise operators
    // -----------------

    bitwise_or:?   [bitwise_or "|"] bitwise_xor
    bitwise_xor:? [bitwise_xor "^"] bitwise_and
    bitwise_and:? [bitwise_and "&"] shift_expr
    shift_expr:?  [shift_expr ("<<"|">>")] sum

    // Arithmetic operators
    // --------------------

    sum:? sum ("+"|"-") term | term
    term:? [term ("*"|"@"|"/"|"%"|"//")] factor
    factor:? ("+"|"-"|"~") factor | power
    power:? await_primary ["**" factor]

    // Primary elements
    // ----------------

    await_primary:? ["await"] primary
    primary:?
          primary "." Name
        | primary "(" [arguments | comprehension] ")"
        | primary "[" slices "]"
        | atom
    slices:? ",".(slice | named_expression | starred_expression)+ [","]
    slice: expression? ":" expression? [":" expression?]
    atom:
          "(" [tuple_content | yield_expr | named_expression | comprehension] ")"
        | "[" [star_named_expressions | comprehension] "]"
        | "{" [dict_content | star_named_expressions | dict_comprehension | comprehension] "}"
        | Name | Number | strings | bytes | "..." | "None" | "True" | "False"

    // Lambda functions
    // ----------------

    lambda: "lambda" [lambda_parameters] ":" expression

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
        | lambda_starred_param ["," ",".lambda_param_maybe_default+] ["," [lambda_double_starred_param ","?]]
        | "*" "," ",".lambda_param_maybe_default+ ["," [lambda_double_starred_param ","?]]
        | lambda_double_starred_param [","]
    lambda_param_no_default: name_definition !"="
    lambda_param_with_default: name_definition "=" expression
    lambda_param_maybe_default: name_definition ["=" expression ]
    lambda_starred_param: "*" name_definition
    lambda_double_starred_param: "**" name_definition

    // LITERALS
    // ========

    fstring: FStringStart fstring_content* FStringEnd
    fstring_content:? FStringString | fstring_expr
    fstring_conversion: "!" Name
    fstring_expr: "{" expressions ["="] [ fstring_conversion ] [ fstring_format_spec ] "}"
    fstring_format_spec: ":" fstring_content*

    strings: (String | fstring)+
    bytes: Bytes+

    tuple_content: star_named_expression "," [star_named_expressions]

    // Dicts
    // -----

    dict_content: ",".(dict_starred | dict_key_value)+ [","]
    dict_starred: "**" bitwise_or
    dict_key_value: expression ":" expression

    // Comprehensions & Generators
    // ---------------------------

    comprehension: named_expression for_if_clauses
    for_if_clauses: async_for_if_clause+
    async_for_if_clause:? ["async"] sync_for_if_clause
    sync_for_if_clause: "for" star_targets "in" disjunction comp_if*
    comp_if: "if" disjunction
    dict_comprehension: dict_key_value for_if_clauses

    // FUNCTION CALL ARGUMENTS
    // =======================

    arguments:
        | ",".(starred_expression | named_expression !"=")+ ["," kwargs?]
        | kwargs
    kwargs:
        | ",".(kwarg | starred_expression)+ ","?
        | ",".(kwarg | starred_expression)+ "," ",".(kwarg | double_starred_expression)+ ","?
        | ",".(kwarg | double_starred_expression)+ ","?
    starred_expression: "*" expression
    double_starred_expression: "**" expression
    kwarg: Name "=" expression

    // ASSIGNMENT TARGETS
    // ==================

    // Generic targets
    // ---------------

    star_targets: ",".star_target+ [","]
    star_target:? "*"? (t_primary | star_target_brackets | name_definition)
    star_target_brackets: "(" [star_targets] ")" | "[" [star_targets] "]"

    single_target: t_primary | name_definition | "(" single_target ")"

    t_primary:?
          (
              t_primary "." Name
            | t_primary "(" [arguments|comprehension] ")"
            | atom
        ) &("."|"["|"(")
        | t_primary "[" slices "]"
        | t_primary "." name_definition

    name_definition: Name

    // Targets for del statements
    // --------------------------

    del_targets: ",".(t_primary | del_t_atom)+ [","]
    del_t_atom:? name_definition | "(" [del_targets] ")" | "[" [del_targets] "]"

);

pub fn parse(code: Box<str>) -> PyTree {
    // TODO is this really the best way? Especially for refactoring?!
    let mut code = code.to_string();
    if !code.ends_with('\n') {
        code += "\n";
    }
    PYTHON_GRAMMAR.parse(code.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_grammar() {
        let tree = parse("{foo: 1}\n".into());
        let root_node = tree.root_node();
        assert_eq!(
            root_node.type_(),
            PyNodeType::Nonterminal(NonterminalType::file)
        );
    }
}
