use parsa_python_cst::{GotoNode, TypeLike};

use crate::{
    Document, GotoGoal, InputPosition, Name, ValueName,
    database::ComplexPoint,
    file::{ClassNodeRef, FuncNodeRef, TypeDocs, TypeVarCallbackReturn},
    format_data::FormatData,
    goto::{GotoResolver, PositionalDocument, with_i_s_non_self},
    inference_state::InferenceState,
    name::{Range, TreeName},
    node_ref::NodeRef,
    recoverable_error,
    type_::{CallableLike, FunctionKind, Type, TypeVarLike, TypeVarLikeUsage, TypeVarVariance},
    type_helpers::Class,
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
            match &n.type_ {
                Type::Self_ => {
                    if let Some(cls) = i_s.current_class() {
                        let mut result = format!("*Self is class {}*", cls.name());
                        let doc = TreeName::with_parent_scope(
                            i_s.db,
                            cls.file,
                            cls.class_storage.parent_scope,
                            cls.node().name(),
                        )
                        .documentation();
                        if !doc.is_empty() {
                            result += ":\n";
                            result += &doc;
                        }
                        result
                    } else {
                        recoverable_error!(
                            "There should to be a current class for Self documentation"
                        );
                        "".into()
                    }
                }
                _ => n.name.documentation().to_string(),
            }
        });
        let (inf, mut results) = resolver.infer_definition();
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return None;
        };

        let db = &self.project.db;
        let mut overwritten_results = vec![];

        let mut known_kind = None;
        let mut type_formatted = if only_docstrings {
            "".into()
        } else {
            let t = inf.as_cow_type(i_s);
            if let Type::Namespace(_) = t.as_ref() {
                // Namespaces need a kind earlier, because goto doesn't work on them
                known_kind = Some("namespace");
            }
            pretty_type_formatting(i_s, &t).into_string()
        };

        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            let kind = n.origin_kind();
            if let Name::TreeName(n) = n
                && let Some(name_def) = n.cst_name.name_def()
            {
                let mut format_type_docs = |docs| match docs {
                    TypeDocs::TypeVarLike(tvl) => {
                        let mut doc = String::default();
                        if let Some(TypeVarCallbackReturn::TypeVarLike(usage)) =
                            i_s.find_parent_type_var(&tvl)
                        {
                            let in_definition = usage.in_definition();
                            let definition = NodeRef::from_link(i_s.db, in_definition);
                            // The definition is just a hint where the TypeVar is defined. It's no
                            // guarantuee that there are always a class or function.
                            if definition.maybe_class().is_some() {
                                let class_ref = ClassNodeRef::from_node_ref(definition);
                                doc += &format!("Bound in class {}", class_ref.name());
                                if let TypeVarLikeUsage::TypeVar(tv) = usage {
                                    let variance = tv.type_var.inferred_variance(
                                        db,
                                        &Class::from_undefined_generics(i_s.db, in_definition),
                                    );
                                    doc += &format!(
                                        "\n{} is {}",
                                        tv.type_var.name(i_s.db),
                                        variance.name().to_lowercase()
                                    );
                                    if matches!(tv.type_var.variance, TypeVarVariance::Inferred) {
                                        doc += " (inferred)";
                                    }
                                }
                            }
                            if definition.maybe_function().is_some() {
                                doc += &format!(
                                    "Bound in function {}",
                                    FuncNodeRef::from_node_ref(definition).qualified_name(i_s.db)
                                );
                            }
                        }
                        overwritten_results.push(doc);
                        let format_data = &FormatData::new_short(db);

                        match tvl {
                            TypeVarLike::TypeVar(type_var) => {
                                format!("TypeVar {}", type_var.format(format_data))
                            }
                            TypeVarLike::TypeVarTuple(tvt) => {
                                format!("TypeVarTuple *{}", tvt.format(format_data))
                            }
                            TypeVarLike::ParamSpec(param_spec) => {
                                format!("ParamSpec **{}", param_spec.format(format_data))
                            }
                        }
                    }
                    TypeDocs::TypeAlias(alias) => {
                        let name = alias.name(db);
                        let type_vars = if alias.type_vars.is_empty() {
                            "".into()
                        } else {
                            alias.type_vars.format(&FormatData::new_short(db))
                        };
                        format!(
                            "{name}{} = {}",
                            type_vars.trim(),
                            alias.type_if_valid().format_short(db)
                        )
                    }
                };

                match name_def.expect_type() {
                    TypeLike::Assignment(assignment) => {
                        if let Some(type_docs) = n
                            .file
                            .name_resolution_for_types(&InferenceState::new(db, n.file))
                            .documentation_for_assignment(assignment)
                        {
                            if !only_docstrings {
                                type_formatted = format_type_docs(type_docs);
                            }
                            return "type";
                        }
                    }
                    TypeLike::TypeAlias(type_alias) => {
                        if let Some(type_docs) = n
                            .file
                            .name_resolution_for_types(&InferenceState::new(db, n.file))
                            .documentation_for_type_alias(type_alias)
                        {
                            if !only_docstrings {
                                type_formatted = format_type_docs(type_docs);
                            }
                            return "type";
                        }
                    }
                    TypeLike::Function(func) => {
                        if let Some(Type::Callable(c)) =
                            NodeRef::new(n.file, func.index()).maybe_type()
                            && matches!(c.kind, FunctionKind::Property { .. })
                        {
                            overwritten_results.push(n.documentation().to_string());
                            if !only_docstrings {
                                type_formatted =
                                    c.format_pretty(&FormatData::new_short(db)).into_string();
                            }
                            return "property";
                        }
                    }
                    TypeLike::TypeParam(type_param) => {
                        if let Some(ComplexPoint::TypeVarLike(tvl)) =
                            NodeRef::new(n.file, type_param.name_def().index()).maybe_complex()
                        {
                            if !only_docstrings {
                                type_formatted =
                                    format_type_docs(TypeDocs::TypeVarLike(tvl.clone()))
                            }
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
        if results.is_empty() && only_docstrings {
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
            } else if let Some(known_kind) = &known_kind {
                out.push('(');
                out += known_kind;
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
                    ["function" | "property" | "type" | "module"] => (),
                    _ => {
                        if known_kind.is_none() {
                            out += name.as_code();
                            out += ": ";
                        }
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
        Type::Module(m) => db.loaded_python_file(*m).qualified_name(db).into(),
        Type::Namespace(n) => n.qualified_name().into(),
        _ => t.format_short(db),
    }
}

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}
