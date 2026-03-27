use parsa_python_cst::{GotoNode, TypeLike};

use crate::{
    Document, GotoGoal, InputPosition, Name, ValueName,
    database::ComplexPoint,
    format_data::FormatData,
    goto::{GotoResolver, PositionalDocument, with_i_s_non_self},
    inference_state::InferenceState,
    name::Range,
    node_ref::NodeRef,
    recoverable_error,
    type_::{CallableLike, FunctionKind, Type},
};

impl<'project> Document<'project> {
    pub fn documentation(
        &self,
        position: InputPosition,
        only_docstrings: bool,
    ) -> anyhow::Result<Option<DocumentationResult<'_>>> {
        let document = self.positional_document(position)?;
        Ok(with_i_s_non_self(
            document.db,
            document.file,
            document.scope,
            |i_s| self.documentation_part2(document, only_docstrings, i_s),
        ))
    }
    fn documentation_part2(
        &self,
        document: PositionalDocument<'project, GotoNode<'project>>,
        only_docstrings: bool,
        i_s: &InferenceState,
    ) -> Option<DocumentationResult<'_>> {
        let mut resolver = GotoResolver::new(document, GotoGoal::Indifferent, |n: ValueName| {
            n.name.documentation().to_string()
        });
        let (inf, mut results) = resolver.infer_definition();
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return None;
        };

        let db = &self.project.db;
        let mut overwritten_results = vec![];

        let mut type_formatted = if only_docstrings {
            "".into()
        } else {
            pretty_type_formatting(i_s, &inf.as_cow_type(i_s)).into_string()
        };

        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            let kind = n.origin_kind();
            if let Name::TreeName(n) = n
                && let Some(name_def) = n.cst_name.name_def()
            {
                match name_def.expect_type() {
                    TypeLike::Assignment(assignment) => {
                        if let Some(type_docs) = n
                            .file
                            .name_resolution_for_types(&InferenceState::new(db, n.file))
                            .documentation_for_assignment(assignment)
                        {
                            type_formatted = type_docs;
                            return "type";
                        }
                    }
                    TypeLike::TypeAlias(type_alias) => {
                        if let Some(type_docs) = n
                            .file
                            .name_resolution_for_types(&InferenceState::new(db, n.file))
                            .documentation_for_type_alias(type_alias)
                        {
                            type_formatted = type_docs;
                            return "type";
                        }
                    }
                    TypeLike::Function(func) => {
                        if let Some(Type::Callable(c)) =
                            NodeRef::new(n.file, func.index()).maybe_type()
                            && matches!(c.kind, FunctionKind::Property { .. })
                        {
                            overwritten_results.push(n.documentation().to_string());
                            type_formatted =
                                c.format_pretty(&FormatData::new_short(db)).into_string();
                            return "property";
                        }
                    }
                    TypeLike::TypeParam(type_param) => {
                        if let Some(ComplexPoint::TypeVarLike(tvl)) =
                            NodeRef::new(n.file, type_param.name_def().index()).maybe_complex()
                        {
                            type_formatted = tvl.format_for_docs(&FormatData::new_short(db))
                        } else {
                            recoverable_error!("Expected a type param to have a saved TypeVarLike")
                        }
                        return "type";
                    }
                    _ => (),
                }
            }
            kind
        });
        let on_name = resolver.infos.node.on_name();
        let declaration_kinds = resolver.goto(true);
        if !overwritten_results.is_empty() {
            results = overwritten_results;
        }
        if results.is_empty() {
            return None;
        }
        results.retain(|doc| !doc.is_empty());

        let docs = results.join("\n\n");
        let documentation = if only_docstrings {
            docs
        } else {
            let mut out = String::default();
            out += "```python\n";
            if !declaration_kinds.is_empty() {
                out.push('(');
                out += &declaration_kinds.join(", ");
                out += ") ";
            }
            if let Some(name) = on_name {
                match declaration_kinds.as_slice() {
                    ["class"] => {
                        // Return the inner part in type[A], because that makes more sense and
                        // looks nicer
                        if type_formatted.starts_with("type[") && type_formatted.ends_with("]") {
                            type_formatted.drain(..5);
                            type_formatted.drain(type_formatted.len() - 1..);
                        }
                    }
                    ["function" | "property" | "type"] => (),
                    _ => {
                        out += name.as_code();
                        out += ": ";
                    }
                }
            }
            out += &type_formatted;
            out += "\n```";
            if !results.is_empty() {
                out += "\n---\n";
                out += &docs;
            }
            out
        };
        Some(DocumentationResult {
            documentation,
            on_symbol_range,
        })
    }
}

fn pretty_type_formatting(i_s: &InferenceState, t: &Type) -> Box<str> {
    let db = i_s.db;
    match t {
        Type::FunctionOverload(o) => format!(
            "Overload(\n    {})",
            o.iter_functions()
                .map(|callable| { callable.format_pretty(&FormatData::new_short(db)) })
                .collect::<Vec<_>>()
                .join("\n    ")
        )
        .into(),
        Type::Callable(c) => c.format_pretty(&FormatData::new_short(db)),
        Type::Type(inner) => {
            let mut out = inner.format_short(db).into_string();
            if let Some(CallableLike::Callable(callable)) =
                t.maybe_callable(&InferenceState::new_in_unknown_file(db))
            {
                let formatted = callable.format_pretty(&FormatData::new_short(db));
                out += "(";
                out += formatted.split_once('(').unwrap().1;
            }
            out.into_boxed_str()
        }
        _ => t.format_short(db),
    }
}

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}
