//! Semantic Tokens helpers
//! Big parts of this file are copied from Rust analyzer

use std::ops;

use lsp_types::{
    Position, SemanticToken, SemanticTokenModifier, SemanticTokenType, SemanticTokens,
};
use zuban_python::SemanticTokenProperties;

macro_rules! define_semantic_token_types {
    (
        standard {
            $($standard:ident),*$(,)?
        }
        custom {
            $(($custom:ident, $string:literal) $(=> $fallback:ident)?),*$(,)?
        }

    ) => {
        pub(crate) mod types {
            use super::SemanticTokenType;
            $(pub(crate) const $standard: SemanticTokenType = SemanticTokenType::$standard;)*
            $(pub(crate) const $custom: SemanticTokenType = SemanticTokenType::new($string);)*
        }

        pub(crate) const SUPPORTED_TYPES: &[SemanticTokenType] = &[
            $(self::types::$standard,)*
            $(self::types::$custom),*
        ];

        #[expect(dead_code)]
        pub(crate) fn standard_fallback_type(token: SemanticTokenType) -> Option<SemanticTokenType> {
            $(
                if token == $custom {
                    None $(.or(Some(self::types::$fallback)))?
                } else
            )*
            { Some(token )}
        }
    };
}

define_semantic_token_types![
    standard {
        COMMENT,
        DECORATOR,
        ENUM_MEMBER,
        ENUM,
        FUNCTION,
        INTERFACE,
        KEYWORD,
        MACRO,
        METHOD,
        NAMESPACE,
        NUMBER,
        OPERATOR,
        PARAMETER,
        PROPERTY,
        STRING,
        STRUCT,
        TYPE_PARAMETER,
        VARIABLE,
        TYPE,
    }

    custom {
        // Rust analyzer defines the custom attributes like this, but we currently don't use any
        //(ANGLE, "angle"),
        //(ARITHMETIC, "arithmetic") => OPERATOR,
    }
];

macro_rules! count_tts {
    () => {0usize};
    ($_head:tt $($tail:tt)*) => {1usize + count_tts!($($tail)*)};
}
macro_rules! define_semantic_token_modifiers {
    (
        standard {
            $($standard:ident),*$(,)?
        }
        custom {
            $(($custom:ident, $string:literal)),*$(,)?
        }

    ) => {
        pub(crate) mod modifiers {
            use super::SemanticTokenModifier;

            $(pub(crate) const $standard: SemanticTokenModifier = SemanticTokenModifier::$standard;)*
            $(pub(crate) const $custom: SemanticTokenModifier = SemanticTokenModifier::new($string);)*
        }

        pub(crate) const SUPPORTED_MODIFIERS: &[SemanticTokenModifier] = &[
            $(SemanticTokenModifier::$standard,)*
            $(self::modifiers::$custom),*
        ];

        const LAST_STANDARD_MOD: usize = count_tts!($($standard)*);
    };
}

define_semantic_token_modifiers![
    // If you add a modifier here, make sure you patch up the following things:
    // - Check SemanticTokensBuilder
    // - Check SemanticTokenProperties in zuban_python and the pretty_properties
    // - Make sure you test it
    standard {
        DECLARATION,
        DEFINITION,
        READONLY,
        STATIC,
        DEPRECATED,
        ABSTRACT,
        ASYNC,
        // MODIFICATION,
        // DOCUMENTATION,
        DEFAULT_LIBRARY,
    }
    custom {
        // Rust analyzer defines it like this:
        // (PUBLIC, "public"),
    }
];

#[derive(Default)]
pub(crate) struct ModifierSet(pub(crate) u32);

impl ModifierSet {
    #[expect(dead_code)]
    pub(crate) fn standard_fallback(&mut self) {
        // Remove all non standard modifiers
        self.0 &= !(!0u32 << LAST_STANDARD_MOD)
    }
}

impl ops::BitOrAssign<SemanticTokenModifier> for ModifierSet {
    fn bitor_assign(&mut self, rhs: SemanticTokenModifier) {
        let idx = SUPPORTED_MODIFIERS
            .iter()
            .position(|it| it == &rhs)
            .unwrap();
        self.0 |= 1 << idx;
    }
}

/// Tokens are encoded relative to each other.
///
/// This is a direct port of <https://github.com/microsoft/vscode-languageserver-node/blob/f425af9de46a0187adb78ec8a46b9b2ce80c5412/server/src/sematicTokens.proposed.ts#L45>
pub(crate) struct SemanticTokensBuilder {
    prev_line: u32,
    prev_char: u32,
    data: Vec<SemanticToken>,
}

impl SemanticTokensBuilder {
    pub(crate) fn new() -> Self {
        Self {
            prev_line: 0,
            prev_char: 0,
            data: Default::default(),
        }
    }

    /// Push a new token onto the builder
    pub(crate) fn push(
        &mut self,
        start: Position,
        token_len: u32,
        type_: SemanticTokenType,
        props: SemanticTokenProperties,
    ) {
        let mut token_modifiers_bitset = ModifierSet::default();
        let mut add = |property, modifier| {
            if property {
                token_modifiers_bitset |= modifier;
            }
        };
        add(props.definition, modifiers::DEFINITION);
        add(props.declaration, modifiers::DECLARATION);
        add(props.in_stdlib, modifiers::DEFAULT_LIBRARY);
        add(props.read_only, modifiers::READONLY);
        add(props.static_, modifiers::STATIC);
        add(props.deprecated, modifiers::DEPRECATED);
        add(props.async_, modifiers::ASYNC);
        add(props.abstract_, modifiers::ABSTRACT);

        let mut push_line = start.line;
        let mut push_char = start.character;

        if !self.data.is_empty() {
            push_line -= self.prev_line;
            if push_line == 0 {
                push_char -= self.prev_char;
            }
        }

        let token = SemanticToken {
            delta_line: push_line,
            delta_start: push_char,
            length: token_len,
            token_type: type_index(type_),
            token_modifiers_bitset: token_modifiers_bitset.0,
        };

        self.data.push(token);

        self.prev_line = start.line;
        self.prev_char = start.character;
    }

    pub(crate) fn build(self) -> SemanticTokens {
        SemanticTokens {
            result_id: None,
            data: self.data,
        }
    }
}

fn type_index(ty: SemanticTokenType) -> u32 {
    SUPPORTED_TYPES.iter().position(|it| *it == ty).unwrap() as u32
}
