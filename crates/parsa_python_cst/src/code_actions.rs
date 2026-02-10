use parsa_python::CodeIndex;

use crate::{Tree, TypeIgnoreComment};

pub struct TypeIgnoreInsertion<'tree> {
    pub insertion_index: CodeIndex,
    preexisting_type_ignore_kind: Option<&'tree str>,
}

impl TypeIgnoreInsertion<'_> {
    pub fn format_for_kind(&self, ignore_kind: &str, error_code: &str) -> Option<String> {
        Some(if let Some(kind) = self.preexisting_type_ignore_kind {
            if kind != ignore_kind {
                // There is already a type: ignore, but with a different kind, e.g. type: ignore
                // instead of zuban: ignore
                return None;
            }
            format!(", {error_code}")
        } else {
            format!("  # {ignore_kind}: ignore[{error_code}]")
        })
    }
}

impl Tree {
    /// Checks where we can insert `type: ignore[<code>]` and `zuban: ignore[<code>]`
    pub fn insertion_point_for_type_ignore(
        &self,
        position: CodeIndex,
    ) -> Option<TypeIgnoreInsertion<'_>> {
        match self.type_ignore_comment_for(position, position) {
            Some(TypeIgnoreComment::WithCodes {
                codes,
                codes_start_at_index,
                kind,
            }) => Some(TypeIgnoreInsertion {
                insertion_index: codes_start_at_index + codes.len() as CodeIndex,
                preexisting_type_ignore_kind: Some(kind),
            }),
            Some(TypeIgnoreComment::WithoutCode) => None,
            None => {
                let line = &self.code()[position as usize..];
                let last_valid_position =
                    position + line.find(['\r', '\n']).unwrap_or_else(|| line.len()) as u32;

                let mut leaf = self.0.leaf_by_position(position);
                while let Some(next) = leaf.next_leaf()
                    && next.start() < last_valid_position
                {
                    leaf = next
                }
                if leaf.end() > last_valid_position {
                    return None;
                }

                Some(TypeIgnoreInsertion {
                    insertion_index: leaf.end(),
                    preexisting_type_ignore_kind: None,
                })
            }
        }
    }
}
