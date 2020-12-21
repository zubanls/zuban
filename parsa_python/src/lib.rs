#![recursion_limit="1024"]
mod tokenizer;

use parsa::{create_grammar, Grammar};
use crate::tokenizer::{PythonToken, PythonTokenType, PythonTokenizer};


create_grammar!(
    static PYTHON_GRAMMAR, struct PythonGrammar, struct PythonTree, 
    struct PythonNode, enum PythonNodeType, PythonTokenizer, PythonToken, PythonTokenType,

    file_input: stmt* Endmarker
    single_input: Newline | simple_stmt | compound_stmt Newline
    eval_input: testlist Newline* Endmarker

    decorator: "@" dotted_name [ "(" [arglist] ")" ] Newline
    decorators: decorator+
    decorated: decorators (classdef | funcdef | async_funcdef)

    async_funcdef: "async" funcdef
    funcdef: "def" Name parameters ["->" test] ":" suite

    parameters: "(" [typedargslist] ")"
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

    stmt: simple_stmt | compound_stmt | Newline
    simple_stmt: small_stmt (";" small_stmt)* [";"] Newline
    small_stmt: (expr_stmt | del_stmt | pass_stmt | flow_stmt |
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
    import_as_names: ",".import_as_name+ [","]
    dotted_as_names: dotted_as_name ("," dotted_as_name)*
    dotted_name: Name ("." Name)*
    global_stmt: "global" Name ("," Name)*
    nonlocal_stmt: "nonlocal" Name ("," Name)*
    assert_stmt: "assert" test ["," test]

    compound_stmt: if_stmt | while_stmt | for_stmt | try_stmt | with_stmt | funcdef | classdef | decorated | async_stmt
    async_stmt: "async" (funcdef | with_stmt | for_stmt)
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
    suite: simple_stmt | Newline Indent stmt+ Dedent

    namedexpr_test: test [":=" test]
    test: or_test ["if" or_test "else" test] | lambdef
    test_nocond: or_test | lambdef_nocond
    lambdef: "lambda" [varargslist] ":" test
    lambdef_nocond: "lambda" [varargslist] ":" test_nocond
    or_test:? and_test ("or" and_test)*
    and_test:? not_test ("and" not_test)*
    not_test:? "not" not_test | comparison
    comparison:? expr (comp_op expr)*
    // <> isn"t actually a valid comparison operator in Python. It"s here for the
    // sake of a __future__ import described in PEP 401 (which really works :-)
    comp_op: "<"|">"|"=="|">="|"<="|"<>"|"!="|"in"|"not" "in"|"is"|"is" "not"
    star_expr: "*" expr
    expr: xor_expr ("|" xor_expr)*
    xor_expr:? and_expr ("^" and_expr)*
    and_expr:? shift_expr ("&" shift_expr)*
    shift_expr:? arith_expr (("<<"|">>") arith_expr)*
    arith_expr:? term (("+"|"-") term)*
    term:? factor (("*"|"@"|"/"|"%"|"//") factor)*
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

    classdef: "class" Name ["(" [arglist] ")"] ":" suite

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
    argument: ( test [comp_for] |
                test ":=" test |
                test "=" test |
                "**" test |
                "*" test )

    comp_iter: comp_for | comp_if
    sync_comp_for: "for" exprlist "in" or_test [comp_iter]
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
        let tree = PYTHON_GRAMMAR.parse("{foo: 1}\n");
        let root_node = tree.get_root_node();
        assert_eq!(root_node.node_type(), Some(PythonNodeType::file_input));
        assert_eq!(root_node.get_extra_data(), 0);
        //dbg!(TokenType::get_map());
        //dbg!(PythonNodeType::get_map());
    }
}
