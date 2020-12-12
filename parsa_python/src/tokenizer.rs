/*
 *  A lot of this module is inspired by parso's tokenizer.
 */
extern crate lazy_static;
extern crate regex;

use std::str;
use std::collections::HashSet;
use regex::Regex;
use parsa::{create_token, CodeIndex};

const FORM_FEED: char = '\x0C';
const HEX_NUMBER: &str = r"0[xX](_?[0-9a-fA-F])+";
const BIN_NUMBER: &str = r"0[bB](_?[01])+";
const OCT_NUMBER: &str = r"0[oO](_?[0-7])+";
const DEC_NUMBER: &str = r"(0(_?0)*|[1-9](_?[0-9])*)";
const EXPONENT: &str = r"[eE][-+]?[0-9](_?[0-9])*";

lazy_static::lazy_static! {
    static ref INT_NUMBER: String = or(&[HEX_NUMBER, BIN_NUMBER, OCT_NUMBER, DEC_NUMBER]);
    static ref EXP_FLOAT: String = or(&[r"[0-9](_?[0-9])*", EXPONENT]);
    static ref POINT_FLOAT: String = or(&[
        r"[0-9](_?[0-9])*\.([0-9](_?[0-9])*)?",
        r"\.[0-9](_?[0-9])*"]) + "(" + EXPONENT + ")?";
    static ref FLOAT_NUMBER: String = or(&[&POINT_FLOAT, &EXP_FLOAT]);
    static ref IMAG_NUMBER: String = or(&[r"[0-9](_?[0-9])*", &FLOAT_NUMBER]) + r"[jJ]";
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
        r"[+\-*/%&@`|^!=<>]=?", r"[\[\](){}]", r"[~;.,@]",
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
    let not_single_quote = r#"[^\r\n'\\]"#;
    let not_double_quote = r#"[^\r\n"\\]"#;
    let with_backslash = r"\\(\r\n?|\n|.)";

    let single = "'".to_owned() + r"(" + with_backslash + "|" + not_single_quote + ")*'";
    let double = "\"".to_owned() + r"(" + with_backslash + "|" + not_double_quote + r#")*""#;
    // ?s: here in regex activates the flag "allow . to match \n"
    let single3 = "'''".to_owned() + r"((?s:\\.|'[^'\\]|'\\.|''[^'\\]|''\\.|[^'\\])*''')?";
    let double3 = "\"\"\"".to_owned() + r#"((?s:\\.|"[^"\\]|"\\.|""[^"\\]|""\\.|[^"\\])*""")?"#;

    "^".to_owned() + &or(prefixes) + &or(&[&single3, &double3, &single, &double])
}

create_token!(struct PythonToken, enum PythonTokenType,
              [Name, Operator, String, Bytes, Number, Endmarker, Newline, ErrorToken,
               Indent, Dedent, ErrorDedent, FStringStart, FStringString, FStringEnd]);


#[derive(Default, Debug)]
pub struct PythonTokenizer<'a> {
    code: &'a str,

    previous_token_was_newline: bool,
    index: usize,
    ended: bool,
    indent_stack: Vec<usize>,
    parentheses_level: usize,
    f_string_stack: Vec<FStringNode>,
}

#[derive(Debug, Clone, Copy)]
enum QuoteType {
    Single,        // '
    Double,        // "
    SingleTriple,  // '''
    DoubleTriple,  // """
}

#[derive(Debug)]
struct FStringNode {
    quote: QuoteType,
    parentheses_level: usize,
    format_spec_count: usize,
}

impl FStringNode {
    #[inline]
    fn open_parentheses(&mut self) {
        self.parentheses_level += 1;
    }

    #[inline]
    fn close_parentheses(&mut self) {
        self.parentheses_level -= 1;
        if self.parentheses_level == 0 {
            // No parentheses means that the format spec is also finished.
            self.format_spec_count = 0
        }
    }

    #[inline]
    fn allow_multiline(&self) -> bool {
        match self.quote {
            QuoteType::Single | QuoteType::Double => false,
            QuoteType::SingleTriple | QuoteType::DoubleTriple => false,
        }
    }

    #[inline]
    fn in_expr(&self) -> bool {
        self.parentheses_level > self.format_spec_count
    }

    #[inline]
    fn in_format_spec(&self) -> bool {
        // In the syntax there can be multiple format_spec's nested: {x:{y:3}}
        !self.in_expr() && self.format_spec_count > 0
    }
}

impl<'a> parsa::Tokenizer<'a, PythonToken> for PythonTokenizer<'a> {
    fn new(code: &'a str) -> Self {
        Self {
            code: code,
            indent_stack: vec!(0),
            previous_token_was_newline: true,
            ..Default::default()
        }
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
        while indentation_count < *self.indent_stack.last().unwrap() {
            if indentation_count > self.indent_stack[self.indent_stack.len() - 2] {
                *self.indent_stack.last_mut().unwrap() = indentation_count;
                return self.new_tok(self.index, false, PythonTokenType::ErrorDedent);//, (lnum, start));
            }
            self.indent_stack.pop();
            return self.new_tok(self.index, false, PythonTokenType::Dedent);//, spos);
        }
        None
    }

    #[inline]
    fn encountered_break_token(&mut self) -> Option<PythonToken> {
        if self.parentheses_level != 0 || self.f_string_stack.len() != 0 {
            self.parentheses_level = 0;
            self.f_string_stack.clear();

            let mut indentation = 0;
            for character in self.code[..self.index].chars().rev() {
                if character == ' ' || character == '\t' {
                    indentation += 1;
                } else if character == '\n' || character == '\r' {
                    // We only want to dedent if the token is on a new line.
                    return self.dedent_if_necessary(indentation)
                } else {
                    return None;
                }
            }
        }
        None
    }

    #[inline]
    fn handle_fstring_stack(&mut self) -> Option<PythonToken> {
        let in_expr = self.get_f_string_tos().in_expr();
        let mut iterator = code_from_start(self.code, self.index).chars().enumerate().peekable();
        while let Some((i, character)) = iterator.next() {
            if (character == '{' || character == '}') && !in_expr {
                if let Some((_, next)) = iterator.next() {
                    if self.get_f_string_tos().in_format_spec() {
                        // If the bracket appears again, we can just continue,
                        // it's part of the string.
                        if next != character {
                            if let Some(t) = self.maybe_fstring_string(i) {
                                return Some(t);
                            }
                        }
                    }
                    return None;
                }
            } else if character == '"' {
                for (j, node) in self.f_string_stack.iter().enumerate() {
                    let quote = node.quote;
                    match quote {
                        QuoteType::Double => return self.end_f_string(i, j, quote),
                        QuoteType::DoubleTriple => {
                            if code_from_start(self.code, self.index + i).starts_with("\"\"\"") {
                                return self.end_f_string(i, j, quote);
                            }
                        },
                        _ => {}
                    }
                }
            } else if character == '\'' {
                for (j, node) in self.f_string_stack.iter().enumerate() {
                    let quote = node.quote;
                    match quote {
                        QuoteType::Single => return self.end_f_string(i, j, quote),
                        QuoteType::SingleTriple => {
                            if code_from_start(self.code, self.index + i).starts_with("'''") {
                                return self.end_f_string(i, j, quote);
                            }
                        },
                        _ => {}
                    }
                }
            } else if character == ':' && in_expr {
                let tos = self.get_f_string_tos();
                if tos.parentheses_level - tos.format_spec_count == 1 {
                    tos.format_spec_count += 1;
                    self.index = i;
                }
                // By returning here, we are making sure that the normal
                // tokenizer returns the as an operator.
                return None;
            } else if character == '\\' {
                if let Some(&(_, next)) = iterator.peek() {
                    if next != '{' && next == '}' {
                        iterator.next();
                        if in_expr {
                            self.index += i;
                            return self.new_tok(self.index - 1, false, PythonTokenType::ErrorToken);
                        }
                    }
                }
            } else if character == '\n' || character == '\r' {
                // Check if there is an f-string on the stack that allows no newlines.
                match self.f_string_stack.iter().enumerate().find(
                        |(_, node)| !node.allow_multiline()) {
                    None => {},
                    Some((j, _)) => {
                        if in_expr {
                            self.f_string_stack.drain(j..);
                            return self.next();
                        } else {
                            return self.maybe_fstring_string(i).or_else(|| {
                                self.f_string_stack.drain(j..);
                                // Since we have removed a few f-strings, it
                                // should be fine to just recurse.
                                self.next()
                            });
                        }
                    }
                }
            } else if character == '#' && in_expr {
                self.index += i;  // The part before was whitespace
                let c = code_from_start(self.code, self.index);
                let length = c.find(&['\n', '\r'] as &[_]).map_or(
                    c.len(), |index| index + 1);
                let start = self.index;
                self.index += length;
                return self.new_tok(start, false, PythonTokenType::ErrorToken);
            } else if character != ' ' && character != '\t' && character != FORM_FEED && in_expr {
                return None
            }
        }
        // We are at the end of the code fragment and only the endmarker/dedent
        // tokens will appear
        None
    }

    #[inline]
    fn get_f_string_tos(&mut self) -> &mut FStringNode {
        // tos = top of stack
        self.f_string_stack.last_mut().unwrap()
    }

    #[inline]
    fn end_f_string(&mut self, string_length: usize, drain_from: usize, quote: QuoteType)
                    -> Option<PythonToken> {
        // This is the same if we are in_expr or not. The string ends no matter
        // what. It's a bit strange that in the expr case it returns an
        // fstring_string first, but this should be fine, since if there's a
        // syntax error in the parser, the error will be there anyway.
        return self.maybe_fstring_string(string_length).or_else(|| {
            self.f_string_stack.drain(drain_from..);
            let start = self.index;
            self.index += match quote {
                QuoteType::Single | QuoteType::Double => 1,
                QuoteType::SingleTriple | QuoteType::DoubleTriple => 3,
            };
            self.new_tok(start, false, PythonTokenType::FStringEnd)
        });
    }

    #[inline]
    fn maybe_fstring_string(&mut self, length: usize) -> Option<PythonToken> {
        if length > 0 {
            let start = self.index;
            self.index += length;
            return self.new_tok(start, false, PythonTokenType::FStringString);
        }
        return None;
    }

    #[inline]
    fn skip_whitespace(&mut self) -> usize {
        let mut indentation = 0;
        let mut was_comment = false;
        let mut iterator = code_from_start(self.code, self.index).chars();
        while let Some(character) = iterator.next() {
            if character == '\n' || character == '\r' {
                if !self.previous_token_was_newline {
                    return indentation;
                }
                was_comment = false;
                indentation = 0;
            } else if !was_comment {
                if character == ' ' || character == '\t' || character == FORM_FEED {
                    if self.previous_token_was_newline {
                        indentation += 1;
                    }
                } else if character == '#' {
                    was_comment = true;
                    indentation = 0;
                } else if character == '\n' || character == '\r' {
                    if !self.previous_token_was_newline {
                        return indentation;
                    }
                    indentation = 0;
                } else if character == '\\' {
                    let mut found_newline = false;
                    if let Some(&c) = self.code.as_bytes().get(self.index + 1) {
                        if c == b'\r' {
                            self.index += 1;
                            found_newline = true
                        }
                    }
                    if let Some(&c) = self.code.as_bytes().get(self.index + 1) {
                        if c == b'\n' {
                            self.index += 1;
                            found_newline = true;
                        }
                    }
                    if !found_newline {
                        return indentation;
                    }
                    self.index += 1;
                    self.skip_whitespace();
                    return indentation;
                } else {
                    break
                }
            }
            self.index += 1;
        }
        indentation
    }
}

impl Iterator for PythonTokenizer<'_> {
    type Item = PythonToken;
    fn next(&mut self) -> Option<Self::Item> {
        if self.ended {
            return None;
        }
        if self.f_string_stack.len() != 0 {
            if let Some(token) = self.handle_fstring_stack() {
                return Some(token);
            }
        }

        let indentation = self.skip_whitespace();

        let start = self.index;
        let c = code_from_start(self.code, self.index);
        if self.previous_token_was_newline {
            self.previous_token_was_newline = false;
            if let Some(&character) = c.as_bytes().first() {
                if character != b'\n' && character != b'\r' {
                    if self.parentheses_level == 0 && self.f_string_stack.len() == 0 {
                        if indentation > *self.indent_stack.last().unwrap() {
                            self.indent_stack.push(indentation);
                            return self.new_tok(start, false, PythonTokenType::Indent);
                        } else {
                            if let Some(token) = self.dedent_if_necessary(start - self.index) {
                                return Some(token);
                            }
                        }
                    }
                }
            }
        }

        if let Some(match_) = OPERATOR.find(c) {
            let character = c.as_bytes()[0];
            if character == b';' {
                self.encountered_break_token();
            }
            self.index += match_.end();

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
            }
            return self.new_tok(start, true, PythonTokenType::Operator);
        }
        if let Some(match_) = NUMBER.find(c) {
            self.index += match_.end();
            return self.new_tok(start, false, PythonTokenType::Number);
        }
        let regexes = [
            (&*STRING, PythonTokenType::String),
            (&*BYTES, PythonTokenType::Bytes),
        ];
        for &(r, token_type) in &regexes {
            if let Some(match_) = r.find(c) {
                let length = match_.end();
                self.index += length;
                if length <= 5 && (match_.as_str().contains("'''")
                                   || match_.as_str().contains("\"\"\"")) {
                    return self.new_tok(start, false, PythonTokenType::ErrorToken);
                }
                return self.new_tok(start, false, token_type);
            }
        }
        if let Some(match_) = F_STRING_START.find(c) {
            self.index += match_.end();
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
            return self.new_tok(start, false, PythonTokenType::FStringStart);
        }

        if let Some(match_) = NAME.find(c) {
            if ALWAYS_BREAK_NAMES.contains(match_.as_str()) {
                self.encountered_break_token();

            }
            self.index += match_.end();
            // TODO we should be using something like Python's str.isidentifier here.
            return self.new_tok(start, true, PythonTokenType::Name);
        }

        if let Some(match_) = NEWLINE.find(c) {
            self.index += match_.end();
            if self.parentheses_level == 0 && self.f_string_stack.len() == 0 {
                self.previous_token_was_newline = true;
                return self.new_tok(start, false, PythonTokenType::Newline);
            } else {
                return self.next();
            }
        }

        match c.as_bytes().first() {
            None => {
                if self.indent_stack.len() != 1 {
                    self.indent_stack.pop();
                    self.new_tok(start, false, PythonTokenType::Dedent)
                } else {
                    self.ended = true;
                    self.new_tok(start, false, PythonTokenType::Endmarker)
                }
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

#[cfg(test)]
mod tests {
    use parsa::Tokenizer;
    use super::*;
    use PythonTokenType::*;

    macro_rules! parametrize {
        ($($name:ident $input:expr => $expected:tt;)*) => {$(
            #[test]
            fn $name() {
                let string: &str = $input;
                let tokenizer = PythonTokenizer::new($input);
                let actual: Vec<_> = tokenizer.map(|t| (t.start_index as usize, t.length, t.type_)).collect();
                let mut expected = vec!$expected;
                expected.push((string.len(), 0, Endmarker));
                assert_eq!(actual, expected);
            }
        )*}
    }

    parametrize!(
        simple "asdf + 11" => [(0, 4, Name), (5, 1, Operator), (7, 2, Number)];
        unicode "我あφ()" => [(0, 8, Name), (8, 1, Operator), (9, 1, Operator)];
        string1 r#"u"test""# => [(0, 7, String)];
        string2 r#"u"""test""""# => [(0, 11, String)];
        string3 r#"U"""test""""# => [(0, 11, String)];
        string4 "u'''test'''" => [(0, 11, String)];
        string5 "U'''test'''" => [(0, 11, String)];
        string6 "r'''test'''" => [(0, 11, String)];
        string7 "R'''test'''" => [(0, 11, String)];
        string_with_escape1 r"'''test\''''" => [(0, 12, String)];
        string_with_escape2 r"R'''test\''''" => [(0, 13, String)];
        string_with_escape3 r"''\'test\''''" => [(0, 2, String), (2, 1, ErrorToken),
                                                 (3, 8, String), (11, 2, String)];
        bytes1 "b'foo'" => [(0, 6, Bytes)];
        bytes2 "br'foo'" => [(0, 7, Bytes)];
        bytes3 "rb'foo'" => [(0, 7, Bytes)];
        bytes4 "Rb'foo'" => [(0, 7, Bytes)];
        bytes5 "RB'foo'" => [(0, 7, Bytes)];
        bytes6 "B'foo'" => [(0, 6, Bytes)];
        bytes7 r#"B"foo""# => [(0, 6, Bytes)];
        bytes8 r#"rB"foo""# => [(0, 7, Bytes)];
        bytes9 r#"Br"foo""# => [(0, 7, Bytes)];
        multiline_string_error1 "''''\n" => [(0, 3, ErrorToken), (3, 1, ErrorToken), (4, 1, Newline)];
        multiline_string_error2 "'''" => [(0, 3, ErrorToken)];
        multiline_string_error3 "'''''" => [(0, 3, ErrorToken), (3, 2, String)];
        single_line_string_error1 "' \n'" => [(0, 1, ErrorToken), (2, 1, Newline), (3, 1, ErrorToken)];

        backslash1 "\\\nfoo" => [(2, 3, Name)];
        backslash2 " \\\nfoo" => [(3, 0, Indent), (3, 3, Name), (6, 0, Dedent)];
        backslash3 "\\foo" => [(0, 1, ErrorToken), (1, 3, Name)];
        backslash4 "(+ \\\n 3.5)" => [(0, 1, Operator), (1, 1, Operator), (6, 3, Number), (9, 1, Operator)];
    );
}
