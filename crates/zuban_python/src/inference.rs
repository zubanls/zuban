/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use std::{borrow::Cow, cell::Cell, rc::Rc};

use parsa_python_cst::{
    Atom, DottedImportName, GotoNode, Name as CSTName, NameParent, NodeIndex, Primary,
    PrimaryContent, PrimaryOrAtom, Scope,
};

use crate::{
    database::{Database, ParentScope, PointKind},
    debug,
    file::{ClassInitializer, File, FuncNodeRef, PythonFile},
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::{LookupKind, ResultContext},
    name::{ModuleName, Name, NodeName, TreeName},
    node_ref::NodeRef,
    recoverable_error,
    type_::{LookupResult, Type, TypeVarLikeName, TypeVarName, UnionType},
    type_helpers::TypeOrClass,
    InputPosition, ValueName,
};

pub(crate) struct PositionalDocument<'db, T> {
    pub db: &'db Database,
    pub file: &'db PythonFile,
    pub scope: Scope<'db>,
    pub node: T,
}

impl<'db> PositionalDocument<'db, GotoNode<'db>> {
    pub fn for_goto(db: &'db Database, file: &'db PythonFile, pos: InputPosition) -> Self {
        let position = pos.to_code_index(file);
        let (scope, node) = file.tree.goto_node(position);
        debug!(
            "Position for goto-like operation {}->{pos:?} on leaf {node:?}",
            file.file_path(&db),
        );
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        Self {
            db,
            file,
            scope,
            node,
        }
    }

    fn infer_position(&self) -> Option<Inferred> {
        match self.node {
            GotoNode::Name(name) => self.infer_name(name),
            GotoNode::Primary(primary) => Some(self.infer_primary(primary)),
            GotoNode::Atom(atom) => Some(self.infer_atom(atom)),
            GotoNode::None => None,
        }
    }
}

impl<'db, T> PositionalDocument<'db, T> {
    pub fn with_i_s<R>(&self, callback: impl FnOnce(&InferenceState) -> R) -> R {
        with_i_s_non_self(self.db, self.file, self.scope, callback)
    }

    fn infer_name(&self, name: CSTName) -> Option<Inferred> {
        match name.parent() {
            NameParent::NameDef(name_def) => self.maybe_inferred_node_index(name_def.index()),
            NameParent::Atom(atom) => Some(self.infer_atom(atom)),
            NameParent::DottedImportName(dotted_name) => {
                Some(self.infer_dotted_import_name(0, Some(dotted_name)))
            }
            other => {
                debug!("TODO infer {other:?}");
                None
            }
        }
        /*
        let p = node_ref.point();
        if p.calculated() {
            if p.kind() == PointKind::Redirect {
                let redirected_to = p.as_redirected_node_ref(self.db);
            }
        }
        */
    }

    pub fn infer_atom(&self, atom: Atom) -> Inferred {
        self.with_i_s(|i_s| {
            self.file
                .inference(i_s)
                .infer_atom(atom, &mut ResultContext::Unknown)
        })
    }

    fn maybe_inferred_node_index(&self, node_index: NodeIndex) -> Option<Inferred> {
        let n = NodeRef::new(self.file, node_index);
        self.with_i_s(|i_s| n.maybe_inferred(i_s))
    }

    pub fn infer_primary(&self, primary: Primary) -> Inferred {
        self.with_i_s(|i_s| {
            self.file
                .inference(i_s)
                .infer_primary(primary, &mut ResultContext::ExpectUnused)
        })
    }

    pub fn infer_dotted_import_name(
        &self,
        dots: usize,
        dotted: Option<DottedImportName>,
    ) -> Inferred {
        let mut import_result = None;
        if dots > 0 {
            // TODO dots
            return Inferred::new_any_from_error();
        }
        if let Some(dotted) = dotted {
            import_result = self.with_i_s(|i_s| {
                self.file
                    .inference(i_s)
                    .cache_import_dotted_name(dotted, import_result)
            })
        }
        if let Some(import_result) = import_result {
            import_result.as_inferred()
        } else {
            Inferred::new_any_from_error()
        }
    }

    pub fn infer_primary_or_atom(&self, p_or_a: PrimaryOrAtom) -> Inferred {
        match p_or_a {
            PrimaryOrAtom::Primary(p) => self.infer_primary(p),
            PrimaryOrAtom::Atom(a) => self.infer_atom(a),
        }
    }
}

pub(crate) fn with_i_s_non_self<'db, R>(
    db: &'db Database,
    file: &PythonFile,
    scope: Scope,
    callback: impl FnOnce(&InferenceState<'db, '_>) -> R,
) -> R {
    let had_error = &Cell::new(false);
    let parent_scope = match scope {
        Scope::Module => ParentScope::Module,
        Scope::Function(index) => ParentScope::Function(index),
        Scope::Class(index) => ParentScope::Class(index),
        Scope::Lambda(lambda) => {
            return with_i_s_non_self(db, file, lambda.parent_scope(), callback)
        }
    };
    InferenceState::run_with_parent_scope(db, file, parent_scope, |i_s| {
        callback(&i_s.with_mode(Mode::AvoidErrors { had_error }))
    })
}

pub(crate) struct GotoResolver<'db, C> {
    pub infos: PositionalDocument<'db, GotoNode<'db>>,
    pub on_result: C,
}

impl<'db, C> GotoResolver<'db, C> {
    pub(crate) fn new(infos: PositionalDocument<'db, GotoNode<'db>>, on_result: C) -> Self {
        Self { infos, on_result }
    }
}

impl<'db, C: for<'a> Fn(&dyn Name) -> T + Copy + 'db, T> GotoResolver<'db, C> {
    pub fn goto(self, follow_imports: bool) -> Vec<T> {
        if let Some(names) = self.goto_name() {
            return names;
        }
        let callback = self.on_result;
        GotoResolver {
            infos: self.infos,
            on_result: &|n: ValueName| callback(&n),
        }
        .infer_type_definition()
    }

    fn goto_name(&self) -> Option<Vec<T>> {
        let db = self.infos.db;
        let file = self.infos.file;
        let callback_if_name = |node_ref: NodeRef| {
            let n = node_ref.maybe_name()?;
            let tree_name = TreeName::new(db, node_ref.file, ParentScope::Module, n);
            Some((self.on_result)(&tree_name))
        };
        let lookup_on_name = |name: CSTName| {
            // TODO fix parent_scope
            let p = file.points.get(name.index());
            if p.calculated() && p.kind() == PointKind::Redirect {
                let node_ref = p.as_redirected_node_ref(db);
                callback_if_name(node_ref).map(|r| vec![r])
            } else {
                None
            }
        };
        match self.infos.node {
            GotoNode::Name(name) => lookup_on_name(name),
            GotoNode::Primary(primary) => match primary.second() {
                PrimaryContent::Attribute(name) => lookup_on_name(name).or_else(|| {
                    let base = self.infos.infer_primary_or_atom(primary.first());
                    let mut results = vec![];
                    self.infos.with_i_s(|i_s| {
                        for t in unpack_union_types(db, base.as_cow_type(i_s))
                            .iter_with_unpacked_unions(db)
                        {
                            let lookup = t.lookup(
                                i_s,
                                file,
                                name.as_code(),
                                LookupKind::Normal,
                                &mut ResultContext::Unknown,
                                &|_issue| (),
                                &|_t_of_attr_error| (),
                            );
                            if let LookupResult::GotoName { name, .. } = lookup {
                                if let Some(result) = callback_if_name(NodeRef::from_link(db, name))
                                {
                                    results.push(result);
                                    continue;
                                }
                            }
                            if let Some(inf) = lookup.into_maybe_inferred() {
                                let t = inf.as_cow_type(i_s);
                                type_to_name(i_s, file, &t, &mut |name| {
                                    results.push((self.on_result)(name))
                                })
                            }
                        }
                    });
                    (!results.is_empty()).then_some(results)
                }),
                _ => None,
            },
            GotoNode::Atom(_) | GotoNode::None => None,
        }
    }
}

impl<'db, C: for<'a> Fn(ValueName) -> T + Copy + 'db, T> GotoResolver<'db, C> {
    pub fn infer_type_definition(&self) -> Vec<T> {
        let mut result = vec![];
        let Some(inf) = self.infos.infer_position() else {
            return result;
        };
        let callback = self.on_result;
        let file = self.infos.file;
        let db = self.infos.db;
        let scope = self.infos.scope;
        with_i_s_non_self(db, file, scope, |i_s| {
            for type_ in inf.as_cow_type(i_s).iter_with_unpacked_unions(db) {
                debug!(
                    "Part of inferring type definition: {:?}",
                    type_.format_short(db)
                );
                type_to_name(i_s, file, &type_, &mut |name| {
                    result.push(callback(ValueName { name, db, type_ }))
                })
            }
        });
        result
    }

    pub fn infer_implementation(&self) -> Vec<T> {
        // TODO should goto stub
        self.infer_type_definition()
    }
}

fn type_to_name<'db>(
    i_s: &InferenceState<'db, '_>,
    file: &'db PythonFile,
    t: &Type,
    add: &mut impl FnMut(&dyn Name),
) {
    let db = i_s.db;
    let from_node_ref = |node_ref: NodeRef<'db>| {
        TreeName::new(
            db,
            node_ref.file,
            ParentScope::Module,
            node_ref.expect_name(),
        )
    };
    let from_type_var_like_name = |tvl_name| match tvl_name {
        TypeVarLikeName::InString { name_node, .. } => {
            from_node_ref(NodeRef::from_link(db, name_node))
        }
        TypeVarLikeName::SyntaxNode(link) => {
            from_node_ref(NodeRef::from_link(db, link).name_ref_of_name_def())
        }
    };
    let from_class_node_ref = |node_ref| {
        let parent_scope = ClassInitializer::from_node_ref(node_ref)
            .class_storage
            .parent_scope;
        TreeName::new(db, node_ref.file, parent_scope, node_ref.node().name())
    };
    let lookup = |module: &'db PythonFile, name| Some(from_node_ref(module.lookup_symbol(name)?));
    match t {
        Type::Class(c) => add(&from_class_node_ref(c.node_ref(db))),
        Type::None => {
            if let Some(n) = lookup(db.python_state.types(), "NoneType") {
                add(&n)
            }
        }
        Type::Tuple(tup) => {
            let node_ref = tup.class(db).node_ref.to_db_lifetime(db);
            add(&TreeName::new(
                db,
                node_ref.file,
                ParentScope::Module,
                node_ref.node().name(),
            ))
        }
        Type::Any(_) => (),
        Type::Intersection(intersection) => {
            for t in intersection.iter_entries() {
                type_to_name(i_s, file, &t, add);
            }
        }
        Type::FunctionOverload(overload) => {
            let first = overload.iter_functions().next().unwrap();
            type_to_name(i_s, file, &Type::Callable(first.clone()), add)
        }
        Type::TypeVar(tv) => match tv.type_var.name {
            TypeVarName::Name(tvl_name) => add(&from_type_var_like_name(tvl_name)),
            TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => (),
        },
        Type::Type(t) => return type_to_name(i_s, file, &t, add),
        Type::Callable(callable) => {
            let node_ref = NodeRef::from_link(db, callable.defined_at);
            if let Some(func) = node_ref.maybe_function() {
                let parent_scope = FuncNodeRef::from_node_ref(node_ref).parent_scope();
                add(&TreeName::new(db, node_ref.file, parent_scope, func.name()))
            } else if let Some(callable) = lookup(db.python_state.typing(), "Callable") {
                add(&callable)
            }
        }
        Type::RecursiveType(rec) => type_to_name(i_s, file, rec.calculated_type(db), add),
        Type::NewType(n) => add(&from_node_ref(NodeRef::from_link(db, n.name_node))),
        Type::ParamSpecArgs(usage) | Type::ParamSpecKwargs(usage) => {
            add(&from_type_var_like_name(usage.param_spec.name))
        }
        Type::Literal(l) => {
            let node_ref = l.fallback_node_ref(db);
            add(&TreeName::new(
                db,
                node_ref.file,
                ParentScope::Module,
                node_ref.node().name(),
            ))
        }
        Type::Dataclass(dataclass) => add(&from_class_node_ref(dataclass.class.node_ref(db))),
        // It seems like dataclass transform is only used as an internal type
        Type::DataclassTransformObj(_) => (),
        Type::TypedDict(_td) => todo!(),
        Type::NamedTuple(_) => todo!(),
        Type::Enum(enum_) => {
            if enum_.from_functional_definition(db) {
                add(&NodeName::new(
                    db,
                    NodeRef::from_link(db, enum_.defined_at),
                    enum_.name.as_str(db),
                ))
            } else {
                add(&from_class_node_ref(*enum_.class(db)))
            }
        }
        Type::EnumMember(member) => {
            if let Some(node_ref) = member.name_node(db) {
                add(&from_node_ref(node_ref))
            } else {
                // If we have no name we just goto the enum.
                type_to_name(i_s, file, &Type::Enum(member.enum_.clone()), add)
            }
        }
        Type::Module(file_index) => add(&ModuleName {
            db,
            file: db.loaded_python_file(*file_index),
        }),
        Type::Namespace(_) => {
            // Namespaces cannot be used in goto
        }
        Type::Super { class, .. } => {
            // TODO this only cares about one class, when it could care about all bases
            for base in class.class(db).bases(db) {
                if let TypeOrClass::Class(base) = base {
                    type_to_name(i_s, file, &base.as_type(db), add)
                }
            }
        }
        Type::CustomBehavior(_) => {
            debug!("TODO implement goto for custom behavior");
        }
        Type::Self_ => {
            if let Some(cls) = i_s.current_class() {
                type_to_name(i_s, file, &cls.as_type(db), add)
            } else {
                recoverable_error!("Could not find the current class for Self");
            }
        }
        Type::Union(union) => {
            // This shouldn't typically be reached, because we iterate over unions above
            for t in union.iter() {
                type_to_name(i_s, file, t, add)
            }
        }
        Type::Never(_) => (),
    }
}

pub(crate) fn unpack_union_types<'a>(db: &Database, t: Cow<'a, Type>) -> Cow<'a, Type> {
    if t.iter_with_unpacked_unions(db)
        .any(|t| matches!(t, Type::Type(x) if x.is_union_like(db)))
    {
        return Cow::Owned(Type::Union(UnionType::from_types(
            t.iter_with_unpacked_unions(db)
                .map(|t| {
                    let mut unpacked = None;
                    let mut non_unpacked = None;
                    match t {
                        Type::Type(t) if t.is_union_like(db) => {
                            unpacked = Some(
                                t.iter_with_unpacked_unions(db)
                                    .map(|t| Type::Type(Rc::new(t.clone()))),
                            )
                        }
                        _ => non_unpacked = Some(t.clone()),
                    };
                    unpacked
                        .into_iter()
                        .flatten()
                        .chain(non_unpacked.into_iter())
                })
                .flatten()
                .collect(),
            true,
        )));
    }
    t
}
