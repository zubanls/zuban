#![recursion_limit="1024"]
extern crate regex;

use parsa::{create_token, create_grammar, Grammar};


struct JsonTokenizer<'a> {
    code: &'a str,
    index: u32,
}

impl JsonTokenizer<'_> {
    fn new_tok(&self) -> JsonToken {
        JsonToken {
            start_index: 0,
            length: 0,
            type_: TokenType::Endmarker,
            can_contain_syntax: false,
        }
    }
}

impl<'a> parsa::Tokenizer<'a, JsonToken> for JsonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        assert!(code.len() < u32::MAX as usize);
        Self {code: code, index: 0}
    }
}

impl Iterator for JsonTokenizer<'_> {
    type Item = JsonToken;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

create_token!(struct JsonToken, enum TokenType, [Label, String, Number, Endmarker]);

create_grammar!(
    static JSON_GRAMMAR, struct JsonGrammar, struct JsonTree, 
    struct JsonNode, enum NodeType, JsonTokenizer, JsonToken, TokenType,

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
    JSON_GRAMMAR.parse("asdf");
}
