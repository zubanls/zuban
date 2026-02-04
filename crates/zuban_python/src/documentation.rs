use crate::{
    Document, GotoGoal, InputPosition, Name, ValueName,
    format_data::FormatData,
    goto::GotoResolver,
    inference_state::InferenceState,
    name::Range,
    node_ref::NodeRef,
    type_::{CallableLike, FunctionKind, Type},
};

impl<'project> Document<'project> {
    pub fn documentation(
        &self,
        position: InputPosition,
        only_docstrings: bool,
    ) -> anyhow::Result<Option<DocumentationResult<'_>>> {
        let mut resolver = GotoResolver::new(
            self.positional_document(position)?,
            GotoGoal::Indifferent,
            |n: ValueName| n.name.documentation().to_string(),
        );
        let (inf, mut results) = resolver.infer_definition();
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return Ok(None);
        };

        let db = &self.project.db;
        let mut overwritten_results = vec![];

        let mut type_formatted = resolver.infos.with_i_s(|i_s| {
            if only_docstrings {
                "".into()
            } else {
                pretty_type_formatting(i_s, &inf.as_cow_type(i_s)).into_string()
            }
        });

        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            let kind = n.origin_kind();
            if let Name::TreeName(n) = n
                && let Some(name_def) = n.cst_name.name_def()
                && let Some(func) = name_def.maybe_name_of_func()
                && let Some(Type::Callable(c)) = NodeRef::new(n.file, func.index()).maybe_type()
                && matches!(c.kind, FunctionKind::Property { .. })
            {
                overwritten_results.push(n.documentation().to_string());
                type_formatted = c.format_pretty(&FormatData::new_short(db)).into_string();
                return "property";
            }
            kind
        });
        let on_name = resolver.infos.node.on_name();
        let declaration_kinds = resolver.goto(true);
        if !overwritten_results.is_empty() {
            results = overwritten_results;
        }
        if results.is_empty() {
            return Ok(None);
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
                    ["function" | "property"] => (),
                    ["type"] => {
                        out += name.as_code();
                        out += " = ";
                    }
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
        Ok(Some(DocumentationResult {
            documentation,
            on_symbol_range,
        }))
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
