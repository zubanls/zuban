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
        let mut types = vec![];
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
                    types.push(
                        n.maybe_pretty_function_type()
                            .unwrap_or_else(|| n.type_description())
                            .into_string(),
                    );
                }
                n.name.documentation().to_string()
            },
        );
        let mut results = resolver.infer_definition();
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return Ok(None);
        };

        let db = &self.project.db;
        let mut overwritten_results = vec![];
        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            let kind = n.origin_kind();
            if let Name::TreeName(n) = n
                && let Some(name_def) = n.cst_name.name_def()
                && let Some(func) = name_def.maybe_name_of_func()
                && let Some(Type::Callable(c)) = NodeRef::new(n.file, func.index()).maybe_type()
                && matches!(c.kind, FunctionKind::Property { .. })
            {
                overwritten_results.push(n.documentation().to_string());
                types = vec![c.format_pretty(&FormatData::new_short(db)).into_string()];
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
                        for ty in &mut types {
                            if ty.starts_with("type[") && ty.ends_with("]") {
                                ty.drain(..5);
                                ty.drain(ty.len() - 1..);
                            }
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
            if let [description] = types.as_slice()
                && let Some(class_t) = class_t
                && let Some(CallableLike::Callable(callable)) =
                    class_t.maybe_callable(&InferenceState::new_in_unknown_file(db))
            {
                out += description;
                let formatted = callable.format_pretty(&FormatData::new_short(db));
                out += "(";
                out += formatted.split_once('(').unwrap().1;
            } else {
                out += &types.join(" | ");
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

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}
