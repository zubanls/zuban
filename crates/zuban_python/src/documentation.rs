use crate::{
    Document, GotoGoal, InputPosition, Name, ValueName,
    database::Database,
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
        let mut class_t = None;
        let mut resolver = GotoResolver::new(
            self.positional_document(position)?,
            GotoGoal::Indifferent,
            |n: ValueName| {
                if !only_docstrings {
                    if class_t.is_none()
                        && let Type::Type(_) = n.type_
                    {
                        class_t = Some(n.type_.clone())
                    }
                }
                n.name.documentation().to_string()
            },
        );
        let (inf, mut results) = resolver.infer_definition();
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return Ok(None);
        };

        let db = &self.project.db;
        let mut overwritten_results = vec![];

        let mut type_formatted = resolver
            .infos
            .with_i_s(|i_s| pretty_type_formatting(db, &inf.as_cow_type(i_s)).into_string());

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
            class_t = None;
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
            if let Some(class_t) = class_t
                && let Some(CallableLike::Callable(callable)) =
                    class_t.maybe_callable(&InferenceState::new_in_unknown_file(db))
            {
                let formatted = callable.format_pretty(&FormatData::new_short(db));
                out += "(";
                out += formatted.split_once('(').unwrap().1;
            }
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

fn pretty_type_formatting(db: &Database, t: &Type) -> Box<str> {
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
        _ => t.format_short(db),
    }
}

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}
