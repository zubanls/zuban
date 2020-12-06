/*
 *  A lot of this module is inspired by parso's tokenizer.
 */
extern crate lazy_static;
extern crate regex;

use std::str;
use std::collections::HashSet;
use regex::Regex;
use parsa::{create_token, CodeIndex};

const HEX_NUMBER: &str = r"0[xX](_?[0-9a-fA-F])+";
const BIN_NUMBER: &str = r"0[bB](_?[01])+";
const OCT_NUMBER: &str = r"0[oO](_?[0-7])+";
const DEC_NUMBER: &str = r"(0(_?0)*|[1-9](_?[0-9])*)";
const EXPONENT: &str = r"[eE][-+]?[0-9](?:_?[0-9])*";

lazy_static::lazy_static! {
    static ref WHITESPACE: Regex = r(r"^[\f\t ]*#[^\r\n]*");

    static ref INT_NUMBER: String = or(&[HEX_NUMBER, BIN_NUMBER, OCT_NUMBER, DEC_NUMBER]);
    static ref EXP_FLOAT: String = or(&[r"[0-9](_?[0-9])*", EXPONENT]);
    static ref POINT_FLOAT: String = or(&[
        r"[0-9](?:_?[0-9])*\.(?:[0-9](?:_?[0-9])*)?",
        r"\.[0-9](?:_?[0-9])*"]) + "(" + EXPONENT + ")?";
    static ref FLOAT_NUMBER: String = or(&[&POINT_FLOAT, &EXP_FLOAT]);
    static ref IMAG_NUMBER: String = or(&[r"[0-9](?:_?[0-9])*", &FLOAT_NUMBER]) + r"[jJ]";
    static ref NUMBER: Regex = r(&(
        "^".to_owned() + &or(&[&IMAG_NUMBER, &FLOAT_NUMBER, &INT_NUMBER])
    ));

    static ref STRING: Regex = r(&all_string_regexes(&["", "[rR]", "[uU]"]));
    static ref BYTES: Regex = r(&all_string_regexes(&["[bB][rR]?", "[rR][bB]"]));

    // Because of leftmost-then-longest match semantics, be sure to put the
    // longest operators first (e.g., if = came before ==, == would get
    // recognized as two instances of =).
    static ref OPERATOR: Regex = r(&("^".to_owned() + &or(&[
        r"\*\*=?", r">>=?", r"<<=?", r"//=?", r"->", r"\.\.\.", r":=?",
        r"[+\-*/%&@`|^!=<>]=?", r"[\[\](){}", r"[~;.,@]",
    ])));

    static ref NAME: Regex = r(r"^[A-Za-z_0-9\u0080-\uffff]+");
    static ref NEWLINE: Regex = r(r"^(\r\n?|\n)");
    static ref F_STRING_START: Regex = r(r#"^([Ff][Rr]?|[Rr][Ff])('|"|"""|''')"#);

    static ref ALWAYS_BREAK_NAMES: HashSet<&'static str> = [
        "import", "class", "def", "try", "except",
        "finally", "while", "with", "return", "continue",
        "break", "del", "pass", "global", "assert", "nonlocal"
    ].iter().cloned().collect();
}


fn r(regex_string: &str) -> Regex {
    Regex::new(regex_string).unwrap()
}

fn or(regexes: &[&str]) -> String {
    "(".to_owned() + &regexes.join("|") + ")"
}

fn all_string_regexes(prefixes: &[&'static str]) -> String {
    let not_single_quote = r#"[^\r\n'\\]*"#;
    let not_double_quote = r#"[^\r\n"\\]*"#;
    let backslash = r"\\(\r\n?|\n|.)";

    let single = "'".to_owned() + not_single_quote + r"(" + backslash
                 + not_single_quote + ")*'";
    let double = "\"".to_owned() + not_double_quote + r"(" + backslash
                 + not_double_quote + r#")*""#;
    let single3 = "'''".to_owned() + r"(?s:\\.|'[^'\\]|'\\.|''[^'\\]|''\\.|[^'\\])*'''";
    let double3 = r#"""""#.to_owned() + r#"(?s:\\.|"[^"\\]|"\\.|""[^"\\]|""\\.|[^"\\])*""""#;

    "^".to_owned() + &or(prefixes) + &or(&[&single, &double, &single3, &double3])
}

create_token!(struct PythonToken, enum PythonTokenType,
              [Name, Operator, String, Bytes, Number, Endmarker, Newline, ErrorToken,
               Indent, Dedent, ErrorDedent, F_StringStart, F_StringString, F_StringEnd]);


#[derive(Default, Debug)]
pub struct PythonTokenizer<'a> {
    code: &'a str,

    index: usize,
    ended: bool,
    indents: Vec<Indent>,
    parentheses_level: usize,
    f_string_stack: Vec<FStringNode>,
}

#[derive(Debug)]
struct Indent {
    start: CodeIndex,
    indentation_count: usize,
}

#[derive(Debug)]
enum QuoteType {
    Single,
    Double,
    SingleTriple,
    DoubleTriple,
}

#[derive(Debug)]
struct FStringNode {
    quote: QuoteType,
    parentheses_level: usize,
    format_spec_count: usize,
}

impl FStringNode {
    /*
    def __init__(self, quote):
        self.previous_lines = ''
        self.last_string_start_pos = None
        # In the syntax there can be multiple format_spec's nested:
        # {x:{y:3}}
    */

    fn open_parentheses(&mut self) {
        self.parentheses_level += 1;
    }

    fn close_parentheses(&mut self) {
        self.parentheses_level -= 1;
        if self.parentheses_level == 0 {
            // No parentheses means that the format spec is also finished.
            self.format_spec_count = 0
        }
    }

    fn allow_multiline(&self) -> bool {
        match self.quote {
            QuoteType::Single | QuoteType::Double => false,
            QuoteType::SingleTriple | QuoteType::DoubleTriple => false,
        }
    }

    fn is_in_expr(&self) -> bool {
        self.parentheses_level > self.format_spec_count
    }

    fn is_in_format_spec(&self) -> bool {
        !self.is_in_expr() && self.format_spec_count > 0
    }
}

impl<'a> parsa::Tokenizer<'a, PythonToken> for PythonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        Self {code: code, ..Default::default()}
    }

}

impl PythonTokenizer<'_> {
    #[inline]
    fn new_tok(&self, start: usize, can_contain_syntax: bool, type_: PythonTokenType)
            -> Option<PythonToken> {
        Some(PythonToken {
            start_index: start as CodeIndex,
            length: (self.index - start) as CodeIndex,
            type_: type_,
            can_contain_syntax: can_contain_syntax,
        })
    }

    #[inline]
    fn dedent_if_necessary(&mut self, indentation_count: usize) -> Option<PythonToken> {
        while indentation_count < self.indents.last().unwrap().indentation_count {
            if indentation_count > self.indents[self.indents.len() - 2].indentation_count {
                self.indents.last_mut().unwrap().indentation_count = indentation_count;
                return self.new_tok(self.index, false, PythonTokenType::ErrorDedent);//, (lnum, start));
            }
            self.indents.pop();
            return self.new_tok(self.index, false, PythonTokenType::Dedent);//, spos);
        }
        None
    }

    #[inline]
    fn code_from_start(&self) -> &str {
        // This function only exists, because the regex crate is not able to at
        // the beginning of a specific position.
        unsafe {
            str::from_utf8_unchecked(&self.code.as_bytes()[self.index as usize..])
        }
    }

    #[inline]
    fn encountered_break_token(&mut self) {
        self.parentheses_level = 0;
        self.f_string_stack.clear();

        /*
        // We only want to dedent if the token is on a new line.
        m = re.match(r'[ \f\t]*$', line[:start])
        if m is not None:
            yield from dedent_if_necessary(m.end())

            */
    }
}

impl Iterator for PythonTokenizer<'_> {
    type Item = PythonToken;
    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }


        if let Some(match_) = WHITESPACE.find(code_from_start(self.code, self.index)) {
            self.index += match_.end();
        }

        let start = self.index;
        let c = code_from_start(self.code, self.index);
        if let Some(match_) = OPERATOR.find(c) {
            // TODO ; always break
            self.index = match_.end();

            let character = c.as_bytes()[0];
            if character == b'(' || character == b'[' || character == b'{' {
                match self.f_string_stack.last_mut() {
                    None => self.parentheses_level += 1,
                    Some(node) => node.open_parentheses(),
                }
            } else if character == b')' || character == b']' || character == b'}' {
                match self.f_string_stack.last_mut() {
                    None => if self.parentheses_level > 0 {self.parentheses_level -= 1},
                    Some(node) => node.close_parentheses(),
                }
            } else if character == b':' {
                match self.f_string_stack.last_mut() {
                    None => {},
                    Some(node) => {
                        if node.parentheses_level - node.format_spec_count == 1 {
                            // `:` and `:=` might end up here
                            node.format_spec_count += 1;
                            self.index = start + 1;
                        }
                    },
                }
            } else if character == b';' {
                self.encountered_break_token();
            }
            return self.new_tok(start, true, PythonTokenType::Operator);
        }
        let regexes = [
            (&*STRING, PythonTokenType::String),
            (&*BYTES, PythonTokenType::Bytes),
            (&*NUMBER, PythonTokenType::Number)
        ];
        for (r, token_type) in &regexes {
            if let Some(match_) = r.find(c) {
                self.index = match_.end();
                return self.new_tok(start, false, *token_type);
            }
        }
        if let Some(match_) = NAME.find(c) {
            if ALWAYS_BREAK_NAMES.contains(match_.as_str()) {
                self.encountered_break_token();

            }
            self.index = match_.end();
            /*
            if token.isidentifier():
                yield PythonToken(NAME, token, spos, prefix)
            else:
                yield from _split_illegal_unicode_name(token, spos, prefix)
            */
            return self.new_tok(start, true, PythonTokenType::Name);
        }
        if let Some(match_) = NEWLINE.find(c) {
            /*
            if any(not f.allow_multiline() for f in fstring_stack):
                fstring_stack.clear()
            */

            self.index = match_.end();
            if self.parentheses_level == 0 && self.f_string_stack.len() == 0 {
                return self.new_tok(start, false, PythonTokenType::Newline);
            } else {
                return self.next();
            }
        }
        if let Some(match_) = F_STRING_START.find(c) {
            self.index = match_.end();
            self.f_string_stack.push(FStringNode {
                quote: {
                    let string = match_.as_str();
                    if string.contains("''") {
                        QuoteType::SingleTriple
                    } else if string.contains("\"\"") {
                        QuoteType::DoubleTriple
                    } else if string.contains("'") {
                        QuoteType::Single
                    } else {
                        QuoteType::Double
                    }
                },
                parentheses_level: 0,
                format_spec_count: 0,
            });
            return self.new_tok(start, false, PythonTokenType::F_StringStart);
        }

        match c.as_bytes().first() {
            None => {
                self.ended = true;
                self.new_tok(start, false, PythonTokenType::Endmarker)
            },
            Some(_) => {
                self.index += 1;
                self.new_tok(start, false, PythonTokenType::ErrorToken)
            },
        }

    }

}

#[inline]
fn code_from_start(code: &str, index: usize) -> &str {
    // This function only exists, because the regex crate is not able to at
    // the beginning of a specific position.
    unsafe {
        str::from_utf8_unchecked(&code.as_bytes()[index..])
    }
}
