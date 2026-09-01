use parsa_python::CodeIndex;

#[derive(Debug, PartialEq, Eq)]
pub enum TypeIgnoreComment<'db> {
    WithCodes {
        codes: &'db str,
        kind: &'static str,
        codes_start_at_index: CodeIndex,
        codes_of_later_type_ignores: Vec<&'db str>,
    },
    WithoutCode,
}

/// All `# type: ignore` / `# zuban: ignore` comments of a file, scanned once and ordered by
/// position.
#[derive(Debug, Clone, Default)]
pub struct IgnoreDirectives {
    entries: Vec<IgnoreDirective>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IgnoreDirective {
    /// The offset of the `#` that starts the comment containing this directive
    pub hash_start: CodeIndex,
    /// "type" or "zuban"
    pub kind: &'static str,
    /// The span of the raw text within the brackets of e.g. `# type: ignore[a, b]`.
    /// `None` for a bare ignore like `# type: ignore`.
    pub codes_span: Option<(CodeIndex, CodeIndex)>,
}

impl IgnoreDirectives {
    pub fn scan(code: &str) -> Self {
        let mut entries = vec![];
        let mut line_start: CodeIndex = 0;
        for line in code.split(['\n', '\r']) {
            let mut iterator = line.split('#');
            // The first part precedes any `#` and can therefore not contain a comment
            let mut comment_start = line_start + iterator.next().unwrap().len() as CodeIndex + 1;
            for comment in iterator {
                if let Some(directive) = maybe_ignore_directive_in_comment(comment, comment_start) {
                    entries.push(directive);
                }
                comment_start += comment.len() as CodeIndex + 1;
            }
            line_start += line.len() as CodeIndex + 1;
        }
        Self { entries }
    }

    pub fn entries(&self) -> &[IgnoreDirective] {
        &self.entries
    }

    /// Returns the merged ignore comment relevant for an issue with the given span, i.e. all
    /// ignore comments between `start` and the end of the line that contains `end`.
    pub fn type_ignore_comment_for<'code>(
        &self,
        code: &'code str,
        start: CodeIndex,
        end: CodeIndex,
    ) -> Option<TypeIgnoreComment<'code>> {
        // Returns Some(WithoutCode) when there is a type: ignore
        // Returns Some(WithCodes{codes: "foo", ..}) when there is a type: ignore[foo]
        let end_of_last_line = match code[end as usize..].find(['\n', '\r']) {
            Some(newline) => end + newline as CodeIndex,
            None => code.len() as CodeIndex,
        };
        self.fold_in_range(code, start, end_of_last_line)
    }

    /// Merges all directives whose comments start within `start..end`, with the same semantics
    /// the previous per-issue text scan had: multiple coded ignores accumulate their codes, while
    /// any bare ignore makes the result a bare ignore.
    pub(crate) fn fold_in_range<'code>(
        &self,
        code: &'code str,
        start: CodeIndex,
        end: CodeIndex,
    ) -> Option<TypeIgnoreComment<'code>> {
        let first_index = self
            .entries
            .partition_point(|entry| entry.hash_start < start);
        let mut result = None;
        for entry in &self.entries[first_index..] {
            if entry.hash_start >= end {
                break;
            }
            let new = entry.as_type_ignore_comment(code);
            if let Some(old) = &mut result {
                match (old, new) {
                    (
                        TypeIgnoreComment::WithCodes {
                            codes_of_later_type_ignores,
                            ..
                        },
                        TypeIgnoreComment::WithCodes {
                            codes: new_codes, ..
                        },
                    ) => codes_of_later_type_ignores.push(new_codes),
                    (old, _) => *old = TypeIgnoreComment::WithoutCode,
                }
            } else {
                result = Some(new);
            }
        }
        result
    }
}

impl IgnoreDirective {
    pub fn is_bare(&self) -> bool {
        self.codes_span.is_none()
    }

    pub fn codes<'code>(&self, code: &'code str) -> Option<&'code str> {
        self.codes_span
            .map(|(start, end)| &code[start as usize..end as usize])
    }

    fn as_type_ignore_comment<'code>(&self, code: &'code str) -> TypeIgnoreComment<'code> {
        match self.codes_span {
            Some((start, _)) => TypeIgnoreComment::WithCodes {
                codes: self.codes(code).unwrap(),
                kind: self.kind,
                codes_start_at_index: start,
                codes_of_later_type_ignores: vec![],
            },
            None => TypeIgnoreComment::WithoutCode,
        }
    }
}

fn maybe_ignore_directive_in_comment(
    comment: &str,
    comment_start: CodeIndex,
) -> Option<IgnoreDirective> {
    let rest = comment.trim_start_matches(' ');
    let mut kind = "type";
    let ignore = rest.strip_prefix("type:").or_else(|| {
        kind = "zuban";
        rest.strip_prefix("zuban:")
    })?;
    let ignore = ignore.trim_start_matches(' ');
    let type_ignore = maybe_type_ignore(
        kind,
        comment_start + (comment.len() - ignore.len()) as CodeIndex,
        ignore,
    )?;
    Some(IgnoreDirective {
        hash_start: comment_start - 1,
        kind,
        codes_span: match type_ignore {
            TypeIgnoreComment::WithCodes {
                codes,
                codes_start_at_index,
                ..
            } => Some((
                codes_start_at_index,
                codes_start_at_index + codes.len() as CodeIndex,
            )),
            TypeIgnoreComment::WithoutCode => None,
        },
    })
}

pub fn maybe_type_ignore<'db>(
    kind: &'static str,
    start_at: CodeIndex,
    text: &'db str,
) -> Option<TypeIgnoreComment<'db>> {
    if let Some(after) = text.strip_prefix("ignore") {
        let trimmed = after.trim_start_matches(' ');
        let start_at = start_at + (text.len() - trimmed.len()) as CodeIndex;
        let trimmed = trimmed.trim_end_matches(' ');
        if let Some(trimmed) = trimmed.strip_prefix('[')
            && let Some(trimmed) = trimmed.strip_suffix(']')
            && !trimmed.is_empty()
        {
            return Some(TypeIgnoreComment::WithCodes {
                kind,
                codes: trimmed,
                codes_start_at_index: start_at + 1,
                codes_of_later_type_ignores: vec![],
            });
        }

        if after.is_empty() || after.starts_with([' ', '\t']) {
            return Some(TypeIgnoreComment::WithoutCode);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spans(code: &str) -> Vec<(CodeIndex, &'static str, Option<&str>)> {
        IgnoreDirectives::scan(code)
            .entries()
            .iter()
            .map(|entry| (entry.hash_start, entry.kind, entry.codes(code)))
            .collect()
    }

    #[test]
    fn scan_bare_and_coded() {
        assert_eq!(spans("x = 1  # type: ignore\n"), [(7, "type", None)]);
        assert_eq!(
            spans("x = 1  # type: ignore[assignment]\n"),
            [(7, "type", Some("assignment"))]
        );
        // Multiple codes with weird spacing keep the raw bracket interior
        assert_eq!(
            spans("x = 1  # type: ignore   [ a , b ]\n"),
            [(7, "type", Some(" a , b "))]
        );
        // Tolerates missing trailing newline
        assert_eq!(spans("x = 1  # type: ignore"), [(7, "type", None)]);
    }

    #[test]
    fn scan_non_matches() {
        assert_eq!(spans("x = 1  # type: ignored\n"), []);
        assert_eq!(spans("x = 1  # type: ignore_foo\n"), []);
        assert_eq!(spans("x = 1  # type: ignore[]\n"), []);
        assert_eq!(spans("x = 1  # type: ignore[a] trailing\n"), []);
        assert_eq!(spans("x = 1  # types: ignore\n"), []);
        // `ignore` directly followed by a comment end or whitespace is fine though
        assert_eq!(spans("x = 1  # type: ignore more\n"), [(7, "type", None)]);
    }

    #[test]
    fn scan_kinds_and_multiple_comments_per_line() {
        assert_eq!(
            spans("x = 1  # zuban: ignore[foo]\n"),
            [(7, "zuban", Some("foo"))]
        );
        // Note that the conventional way to ignore multiple error codes is the comma syntax
        // (`# type: ignore[a, b]`, a single directive). Multiple ignore comments on one line are
        // nevertheless scanned as separate directives, whose codes accumulate on lookup.
        // A second comment on the same line is scanned separately
        assert_eq!(
            spans("x = 1  # a comment # type: ignore[a]\n"),
            [(19, "type", Some("a"))]
        );
        assert_eq!(
            spans("x = 1  # type: ignore[a] # zuban: ignore[b]\n"),
            [(7, "type", Some("a")), (25, "zuban", Some("b"))]
        );
        assert_eq!(
            spans("x = 1  # type: ignore[a] # type: ignore\n"),
            [(7, "type", Some("a")), (25, "type", None)]
        );
    }

    #[test]
    fn scan_offsets_across_lines() {
        let code = "x = 1\ny = 2  # type: ignore[a]\nz = 3\na = 4  # zuban: ignore\n";
        assert_eq!(spans(code), [(13, "type", Some("a")), (44, "zuban", None)]);
        // Windows line endings
        let code = "x = 1\r\ny = 2  # type: ignore[a]\r\n";
        assert_eq!(spans(code), [(14, "type", Some("a"))]);
    }

    #[test]
    fn lookup_same_line() {
        let code = "x = 1  # type: ignore[a]\ny = 2\n";
        let directives = IgnoreDirectives::scan(code);
        let expected = || {
            Some(TypeIgnoreComment::WithCodes {
                codes: "a",
                kind: "type",
                codes_start_at_index: 22,
                codes_of_later_type_ignores: vec![],
            })
        };
        assert_eq!(directives.type_ignore_comment_for(code, 0, 5), expected());
        // Lookups never look at previous lines
        assert_eq!(directives.type_ignore_comment_for(code, 26, 31), None);
        // Comments before the start of the lookup are not considered
        assert_eq!(directives.type_ignore_comment_for(code, 8, 8), None);
    }

    #[test]
    fn lookup_over_multiple_lines() {
        let code =
            "foo(  # type: ignore[a]\n    1,  # type: ignore[b]\n    2,\n)  # type: ignore\n";
        let directives = IgnoreDirectives::scan(code);
        // A lookup that only spans the first line
        assert_eq!(
            directives.type_ignore_comment_for(code, 0, 3),
            Some(TypeIgnoreComment::WithCodes {
                codes: "a",
                kind: "type",
                codes_start_at_index: 21,
                codes_of_later_type_ignores: vec![],
            })
        );
        // A lookup over the first two lines merges the coded ignores
        assert_eq!(
            directives.type_ignore_comment_for(code, 0, 28),
            Some(TypeIgnoreComment::WithCodes {
                codes: "a",
                kind: "type",
                codes_start_at_index: 21,
                codes_of_later_type_ignores: vec!["b"],
            })
        );
        // A lookup over all lines includes the bare ignore, which wins
        assert_eq!(
            directives.type_ignore_comment_for(code, 0, 59),
            Some(TypeIgnoreComment::WithoutCode)
        );
    }

    #[test]
    fn lookup_bare_ignore_wins_in_both_directions() {
        let code = "foo(  # type: ignore\n    1,  # type: ignore[b]\n)\n";
        let directives = IgnoreDirectives::scan(code);
        assert_eq!(
            directives.type_ignore_comment_for(code, 0, 26),
            Some(TypeIgnoreComment::WithoutCode)
        );
    }
}
