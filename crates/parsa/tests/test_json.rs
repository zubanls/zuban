#![recursion_limit = "1024"]
extern crate lazy_static;
extern crate regex;

use std::str;

use parsa::{create_grammar, create_terminals, Grammar};
use regex::Regex;

lazy_static::lazy_static! {
    static ref WHITESPACE: Regex = Regex::new(r"^\s+").unwrap();
    static ref STRING: Regex = Regex::new(r#"^"[^"]*"|'[^']*'"#).unwrap();
    static ref NUMBER: Regex = Regex::new(r"^[+-]?[0-9]+").unwrap();
    static ref LABEL: Regex = Regex::new(r"^\p{alpha}\w*").unwrap();
    static ref ERROR: Regex = Regex::new(r"^[^\w,:{}\[\]]+").unwrap();
}

struct JsonTokenizer<'a> {
    code: &'a str,
    index: usize,
    ended: bool,
}

impl<'a> parsa::Tokenizer<'a, JsonTerminal> for JsonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        assert!(code.len() < u32::MAX as usize);
        Self {
            code,
            index: 0,
            ended: false,
        }
    }
}

impl Iterator for JsonTokenizer<'_> {
    type Item = JsonTerminal;

    fn next(&mut self) -> Option<Self::Item> {
        let new_token = |start, length, type_: JsonTerminalType, can_contain_syntax| {
            Some(JsonTerminal {
                start_index: start as u32,
                length: length as u32,
                type_,
                can_contain_syntax,
            })
        };
        let code_bytes = &self.code.as_bytes();
        let as_code = |index: usize| unsafe { str::from_utf8_unchecked(&code_bytes[index..]) };

        let whitespace = WHITESPACE.find(as_code(self.index));
        if let Some(match_) = whitespace {
            self.index += match_.end();
        }

        let index = self.index;
        const OPERATORS: &[u8; 6] = b",:{}[]";
        if let Some(byte) = code_bytes.get(self.index) {
            if OPERATORS.contains(byte) {
                self.index += 1;
                return new_token(index, 1, JsonTerminalType::Operator, true);
            }
        } else if self.ended {
            return None;
        } else {
            self.ended = true;
            return new_token(index, 0, JsonTerminalType::Endmarker, false);
        }

        for (regex, type_) in &[
            (&*STRING, JsonTerminalType::String),
            (&*NUMBER, JsonTerminalType::Number),
            (&*LABEL, JsonTerminalType::Label),
            (&*ERROR, JsonTerminalType::Error),
        ] {
            if let Some(match_) = regex.find(as_code(index)) {
                self.index += match_.end();
                return new_token(index, match_.end() - match_.start(), *type_, false);
            }
        }
        unreachable!();
    }
}

create_terminals!(struct JsonTerminal, enum JsonTerminalType, [Label, String, Number, Operator, Error, Endmarker]);

create_grammar!(
    static JSON_GRAMMAR, struct JsonGrammar, struct JsonTree, struct JsonNode,
    enum JsonNodeType, enum JsonNonterminalType, JsonTokenizer, JsonTerminal, JsonTerminalType,
    soft_keywords=[]

    document: json Endmarker
    json: array | object
    value: String | Number | json

    array: "[" [json ("," json)*] "]"
    object: "{" [property ("," property)*] "}"
    property: name ":" value
    name: Label | String
);

#[test]
fn it_works() {
    use JsonNodeType::*;
    use JsonNonterminalType::*;
    use JsonTerminalType::*;
    let tree = JSON_GRAMMAR.parse("{foo: 1}".into());
    let root_node = tree.root_node();
    assert_eq!(root_node.type_(), Nonterminal(document));

    assert_eq!(tree.internal_tree.nodes.len(), 12);
    let expected_list = [
        (0, 0, 8, Nonterminal(document)),
        (10, 0, 8, Nonterminal(json)),
        (0, 0, 8, Nonterminal(object)),
        (1, 0, 1, Keyword),
        (6, 1, 6, Nonterminal(property)),
        (2, 1, 3, Nonterminal(name)),
        (0, 1, 3, Terminal(Label)),
        (1, 4, 1, Keyword),
        (0, 6, 1, Nonterminal(value)),
        (0, 6, 1, Terminal(Number)),
        (0, 7, 1, Keyword),
        (0, 8, 0, Terminal(Endmarker)),
    ];

    for (expected, actual) in expected_list.iter().zip(tree.nodes()) {
        assert_eq!(
            &(
                actual.internal_node.next_node_offset,
                actual.start(),
                actual.length(),
                actual.type_(),
            ),
            expected
        );
    }
}

#[test]
fn complicated_alternatives() {
    // Test an alternative syntax that is not json
    create_grammar!(
        static GRAMMAR, struct TempGrammar, struct TempTree, struct TempNode,
        enum TempNodeType, enum NonterminalType, JsonTokenizer, JsonTerminal, JsonTerminalType,
        soft_keywords=[]

        document: content Endmarker
        content:
            | foo ","+
            | bar ","+
            | foo ":"+
        foo: Label "[" Number "]"
        bar: Label ":"
    );

    GRAMMAR.parse("last[3]::".into());
    GRAMMAR.parse("foo[3],".into());
    GRAMMAR.parse("foo[3],,".into());
    GRAMMAR.parse("bar :,,".into());
    GRAMMAR.parse("bar :,".into());
}

#[test]
#[should_panic(expected = "Found an unreachable alternative in the rule \"content\"")]
fn unreachable_alternatives1() {
    create_grammar!(
        static GRAMMAR, struct TempGrammar, struct TempTree, struct TempNode,
        enum TempNodeType, enum NonterminalType, JsonTokenizer, JsonTerminal, JsonTerminalType,
        soft_keywords=[]

        document: content Endmarker
        content:
            | foo [","]
            | bar [","]
            | foo [":"]
        foo: Label "[" Number "]"
        bar: Label ":"
    );
    GRAMMAR.parse("".into());
}

#[test]
#[should_panic(expected = "Found an unreachable alternative in the rule \"content\"")]
fn unreachable_alternatives2() {
    create_grammar!(
        static GRAMMAR, struct TempGrammar, struct TempTree, struct TempNode,
        enum TempNodeType, enum NonterminalType, JsonTokenizer, JsonTerminal, JsonTerminalType,
        soft_keywords=[]

        document: content Endmarker
        content:
            | foo "(" [","]
            | bar "(" [","]
            | foo "(" [":"]
        foo: Label "[" Number "]"
        bar: Label ":"
    );
    GRAMMAR.parse("".into());
}
