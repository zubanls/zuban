use std::collections::HashSet;

use parsa_python_cst::{GotoNode, NameParent, TypeLike};

use crate::{
    Document, GotoGoal, InputPosition, Name, ValueName,
    file::{FuncNodeRef, TypeDocs, TypeVarCallbackReturn},
    goto::{GotoResolver, HeuristicDetail, PositionalDocument, with_i_s_non_self},
    name::{Range, TreeName},
    prelude::*,
    type_::{FunctionKind, PrettyCallableOptions, TypeGatherer, TypeVarVariance},
};

impl<'project> Document<'project> {
    pub fn documentation(
        &self,
        position: InputPosition,
        only_docstrings: bool,
    ) -> anyhow::Result<Option<DocumentationResult<'_>>> {
        let document = self.positional_document(position)?;
        let _indent = debug_indent();
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
        let db = &self.project.db;

        let mut name_origin = NameOrigin::Other;

        let cloned_doc = document.clone();
        let mut resolver = GotoResolver::new(cloned_doc, GotoGoal::Indifferent, |n: ValueName| {
            match &n.type_ {
                Type::Self_ => {
                    if let Some(cls) = i_s.current_class() {
                        let mut result = format!("*Self is class {}*", cls.name());
                        let doc = TreeName::with_parent_scope(
                            i_s.db,
                            cls.file,
                            cls.class_storage.parent_scope,
                            cls.as_node().name(),
                        )
                        .documentation();
                        if !doc.is_empty() {
                            result += ":\n";
                            result += &doc;
                        }
                        result
                    } else {
                        recoverable_error!(
                            "There should be a current class for Self documentation"
                        );
                        "".into()
                    }
                }
                Type::FunctionOverload(overload) => {
                    name_origin = NameOrigin::Overload;
                    // Overloads can have multiple docstrings, just show them all.
                    let implementation = || {
                        let first_func = overload
                            .iter_functions()
                            .next()?
                            .maybe_original_func_node_ref(db)?;
                        Some(
                            &first_func
                                .maybe_overload()?
                                .implementation
                                .as_ref()?
                                .callable,
                        )
                    };
                    let docs: Vec<_> = overload
                        .iter_functions()
                        .map(|f| f.as_ref())
                        .chain(implementation().into_iter())
                        .filter_map(|c| {
                            let func = c.maybe_original_func_def(db)?;
                            let doc = func.name().clean_docstring();
                            (!doc.is_empty()).then_some(doc)
                        })
                        .collect();
                    docs.join("\n\n")
                }
                t => {
                    if let Type::Callable(c) = t
                        && !c.type_vars.is_empty()
                    {
                        name_origin = NameOrigin::GenericFunction;
                    }
                    n.name.documentation().to_string()
                }
            }
        });
        let (inf, mut results) = resolver.infer_definition(Some(HeuristicDetail::Deep));
        let Some(on_symbol_range) = resolver.on_node_range() else {
            // This is probably not reachable
            return None;
        };

        let mut overwritten_results = vec![];

        let mut known_kind = None;
        let mut type_formatted = if only_docstrings {
            "".into()
        } else {
            let t = inf.typed.as_cow_type(i_s);
            if let Type::Namespace(_) = t.as_ref() {
                // Namespaces need a kind earlier, because goto doesn't work on them
                known_kind = Some("namespace");
            }
            let mut s = pretty_type_formatting(i_s, &t, false).into_string();
            if let Some(heuristic) = inf.heuristic {
                let mut t = heuristic.as_cow_type(i_s);
                let t = t.to_mut();
                if let Type::Union(union) = t {
                    // Here we avoid union entries that have the untyped type vars and therefore show up
                    // as A | A.
                    let mut previous_formatting = HashSet::new();
                    let keep_entries = TypeGatherer::from_iter(
                        union
                            .entries
                            .iter()
                            .filter(|entry| previous_formatting.insert(entry.format_short(db)))
                            .cloned(),
                    );
                    *t = keep_entries.into_type();
                }
                let heuristic = pretty_type_formatting(i_s, &t, true).into_string();
                if s != heuristic {
                    s = format!("{s}\n\nMight be: {heuristic}")
                }
            }
            s
        };

        let was_narrowed = resolver.infos.node.on_name().is_some_and(|name| {
            match name.parent() {
                NameParent::Atom(atom) => {
                    // This feels a bit weird, but is probably a good heuristic. Atom normally
                    // does not define types themselves, but in case of narrowing this is pretty
                    // much always the case. For now I don't know about a better signal.
                    NodeRef::new(resolver.infos.file, atom.index())
                        .maybe_type()
                        .is_some()
                }
                _ => false,
            }
        });

        let resolver = GotoResolver::new(resolver.infos, GotoGoal::Indifferent, |n: Name| {
            let kind = n.origin_kind();
            if let Name::TreeName(n) = n
                && let Some(name_def) = n.cst_name.name_def()
            {
                let mut format_type_docs = |docs, overwritten_results: &mut Vec<_>| {
                    if !only_docstrings {
                        type_formatted = match &docs {
                            TypeDocs::TypeVarLike(tvl) => {
                                let mut doc = String::default();
                                if let Some(TypeVarCallbackReturn::TypeVarLike(usage)) =
                                    i_s.find_parent_type_var(&tvl)
                                {
                                    let in_definition = usage.in_definition();
                                    let definition = NodeRef::from_link(db, in_definition);
                                    // The definition is just a hint where the TypeVar is defined.
                                    // It's no guarantuee that there are always a class or
                                    // function.
                                    if definition.maybe_class().is_some() {
                                        let class_ref = ClassNodeRef::from_node_ref(definition);
                                        doc += &format!("Bound in class `{}`", class_ref.name());
                                        let variance = usage.inferred_variance(
                                            db,
                                            &Class::from_undefined_generics(db, in_definition),
                                        );
                                        doc += &format!(
                                            "\n\n`{}` is `{}`",
                                            usage.name(db),
                                            variance.name().to_lowercase()
                                        );
                                        if matches!(usage.variance(), TypeVarVariance::Inferred) {
                                            doc += " (inferred)";
                                        }
                                    }
                                    if definition.maybe_function().is_some() {
                                        doc += &format!(
                                            "Bound in function `{}`",
                                            FuncNodeRef::from_node_ref(definition)
                                                .qualified_name(db)
                                        );
                                    }
                                }
                                overwritten_results.push(doc);
                                let format_data = &FormatData::new_short(db);

                                match tvl {
                                    TypeVarLike::TypeVar(type_var) => type_var.format(format_data),
                                    TypeVarLike::TypeVarTuple(tvt) => {
                                        format!("*{}", tvt.format(format_data))
                                    }
                                    TypeVarLike::ParamSpec(param_spec) => {
                                        format!("**{}", param_spec.format(format_data))
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
                            TypeDocs::SimpleClassTypeAlias(class) => {
                                format!("{} = {}", name_def.as_code(), class.name())
                            }
                        }
                    }
                    match docs {
                        TypeDocs::TypeVarLike(tvl) => match tvl {
                            TypeVarLike::TypeVar(_) => "TypeVar",
                            TypeVarLike::TypeVarTuple(_) => "TypeVarTuple",
                            TypeVarLike::ParamSpec(_) => "ParamSpec",
                        },
                        TypeDocs::TypeAlias(_) | TypeDocs::SimpleClassTypeAlias(_) => "type alias",
                    }
                };

                match name_def.expect_type() {
                    TypeLike::Assignment(assignment) => {
                        let cleaned = n.cst_name.clean_docstring();
                        if !cleaned.is_empty() {
                            overwritten_results.push(cleaned.into());
                        }
                        // Narrowed assignments should not overwrite the docs, because they might
                        // be different types now.
                        if !was_narrowed
                            && let Some(type_docs) = n
                                .file
                                .name_resolution_for_types(&InferenceState::new(db, n.file))
                                .documentation_for_assignment(assignment)
                        {
                            return format_type_docs(type_docs, &mut overwritten_results);
                        }
                    }
                    TypeLike::TypeAlias(type_alias) => {
                        let cleaned = n.cst_name.clean_docstring();
                        if !cleaned.is_empty() {
                            overwritten_results.push(cleaned.into());
                        }
                        if let Some(type_docs) = n
                            .file
                            .name_resolution_for_types(&InferenceState::new(db, n.file))
                            .documentation_for_type_alias(type_alias)
                        {
                            return format_type_docs(type_docs, &mut overwritten_results);
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
                            return format_type_docs(
                                TypeDocs::TypeVarLike(tvl.clone()),
                                &mut overwritten_results,
                            );
                        } else {
                            recoverable_error!("Expected a type param to have a saved TypeVarLike")
                        }
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

        let results_to_string = |results: Vec<String>| results.join("\n\n");
        let documentation = if only_docstrings {
            results_to_string(results)
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
                    ["function"] => {
                        if matches!(
                            name_origin,
                            NameOrigin::GenericFunction | NameOrigin::Overload
                        ) && let Some(primary) = name.maybe_left_of_primary()
                        {
                            let result = document.infer_primary(primary);
                            results.push(format!(
                                "The {} return type is `{}`",
                                match name_origin {
                                    NameOrigin::Overload => "overload",
                                    _ => "chosen",
                                },
                                result.format_short(i_s)
                            ))
                        }
                    }
                    [
                        "property" | "type" | "type alias" | "TypeVar" | "TypeVarTuple"
                        | "ParamSpec" | "module",
                    ] => (),
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
                out += &results_to_string(results);
            }
            out
        };
        Some(DocumentationResult {
            documentation,
            on_symbol_range,
        })
    }
}

enum NameOrigin {
    Other,
    GenericFunction,
    Overload,
}

fn pretty_type_formatting(i_s: &InferenceState, t: &Type, from_heuristic: bool) -> Box<str> {
    let db = i_s.db;
    let format_callable = |c: &CallableContent| {
        c.format_pretty_detailed(
            &FormatData::new_short(db),
            PrettyCallableOptions {
                try_to_format_default: Some(&|db, name| {
                    let func = c.maybe_original_func_def(db)?;
                    func.params()
                        .iter()
                        .find(|param| param.name_def().as_code() == name)
                        .map(|param| param.default().map(|expr| expr.as_code()))
                        .flatten()
                }),
                ..Default::default()
            },
        )
    };
    match t {
        Type::FunctionOverload(o) => format!(
            "Overload(\n    {})",
            o.iter_functions()
                .map(|callable| format_callable(callable))
                .collect::<Vec<_>>()
                .join("\n    ")
        )
        .into(),
        Type::Callable(c) => format_callable(c),
        Type::Type(inner) => {
            if let Some(CallableLike::Callable(callable)) =
                t.maybe_callable(&InferenceState::new_in_unknown_file(db))
            {
                let mut out = inner.format_short(db).into_string();
                let formatted = format_callable(&callable);
                out += "(";
                out += formatted.split_once('(').unwrap().1;
                out.into_boxed_str()
            } else {
                t.format_short(db)
            }
        }
        Type::Module(m) => {
            let mut s = db.loaded_python_file(*m).qualified_name(db);
            if from_heuristic {
                s.insert_str(0, "module ");
            }
            s.into()
        }
        Type::Namespace(n) => n.qualified_name().into(),
        _ => t.format_short(db),
    }
}

pub struct DocumentationResult<'a> {
    pub documentation: String,
    pub on_symbol_range: Range<'a>,
}
