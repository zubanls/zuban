/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use std::{borrow::Cow, cell::Cell, rc::Rc};

use parsa_python_cst::{
    Atom, DottedName, GotoNode, Name as CSTName, NameParent, NodeIndex, Primary, PrimaryContent,
    PrimaryOrAtom, Scope,
};

use crate::{
    database::{Database, ParentScope, PointKind},
    debug,
    file::{ClassInitializer, File, FuncNodeRef, PythonFile},
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::{LookupKind, ResultContext},
    name::{ModuleName, Name, TreeName},
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
            NameParent::Primary(_) => todo!(),
            NameParent::PrimaryTarget(_) => todo!(),
            NameParent::Kwarg(_) => {
                debug!("TODO kwarg infer");
                None
            }
            NameParent::KeywordPattern(_) => todo!(),
            NameParent::ImportFromAsName(_) => todo!(),
            NameParent::DottedName(dotted_name) => Some(self.infer_import_dotted_name(dotted_name)),
            NameParent::FStringConversion(_) => todo!(),
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

    pub fn infer_import_dotted_name(&self, dotted: DottedName) -> Inferred {
        if let Some(import_result) = self.with_i_s(|i_s| {
            self.file
                .inference(i_s)
                .cache_import_dotted_name(dotted, None)
        }) {
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
        .collect()
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
                                if let Some(name) = type_to_name(i_s, file, &inf.as_cow_type(i_s)) {
                                    results.push((self.on_result)(name.as_name()))
                                }
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
    pub fn infer_type_definition(&self) -> impl Iterator<Item = T> + 'db {
        let inf = self.infos.infer_position();
        let callback = self.on_result;
        let file = self.infos.file;
        let db = self.infos.db;
        let scope = self.infos.scope;
        self.infos
            .with_i_s(|i_s| inf.map(|t| t.as_type(i_s).into_iter_with_unpacked_unions(db, true)))
            .into_iter()
            .flatten()
            .filter_map(move |e| {
                debug!(
                    "Part of inferring type definition: {:?}",
                    e.type_.format_short(db)
                );
                Some(callback(ValueName {
                    name: with_i_s_non_self(db, file, scope, |i_s| {
                        type_to_name(i_s, file, &e.type_)
                    })?
                    .as_name(),
                    db,
                    type_: &e.type_,
                }))
            })
    }

    pub fn infer_implementation(&self) -> impl Iterator<Item = T> + 'db {
        // TODO should goto stub
        self.infer_type_definition()
    }
}

enum NameLike<'db> {
    TreeName(TreeName<'db>),
    ModuleName(ModuleName<'db>),
}

impl NameLike<'_> {
    fn as_name(&self) -> &dyn Name {
        match self {
            NameLike::TreeName(n) => n,
            NameLike::ModuleName(n) => n,
        }
    }
}

fn type_to_name<'db>(
    i_s: &InferenceState<'db, '_>,
    file: &'db PythonFile,
    t: &Type,
) -> Option<NameLike<'db>> {
    let db = i_s.db;
    let from_node_ref = |node_ref: NodeRef<'db>| {
        TreeName::new(
            db,
            node_ref.file,
            ParentScope::Module,
            node_ref.expect_name(),
        )
    };
    let lookup = |module: &'db PythonFile, name| Some(from_node_ref(module.lookup_symbol(name)?));
    Some(NameLike::TreeName(match t {
        Type::Class(c) => {
            let node_ref = c.node_ref(db);
            let parent_scope = ClassInitializer::from_node_ref(node_ref)
                .class_storage
                .parent_scope;
            TreeName::new(db, node_ref.file, parent_scope, node_ref.node().name())
        }
        Type::None => lookup(db.python_state.types(), "NoneType")?,
        Type::Tuple(tup) => {
            let node_ref = tup.class(db).node_ref.to_db_lifetime(db);
            TreeName::new(
                db,
                node_ref.file,
                ParentScope::Module,
                node_ref.node().name(),
            )
        }
        Type::Any(_) => return None,
        Type::Intersection(_) => todo!(),
        Type::FunctionOverload(overload) => {
            let first = overload.iter_functions().next().unwrap();
            return type_to_name(i_s, file, &Type::Callable(first.clone()));
        }
        Type::TypeVar(tv) => match tv.type_var.name {
            TypeVarName::Name(tvl_name) => match tvl_name {
                TypeVarLikeName::InString { name_node, .. } => {
                    from_node_ref(NodeRef::from_link(db, name_node))
                }
                TypeVarLikeName::SyntaxNode(_) => todo!(),
            },
            TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => return None,
        },
        Type::Type(t) => return type_to_name(i_s, file, &t),
        Type::Callable(callable) => {
            let node_ref = NodeRef::from_link(db, callable.defined_at);
            if let Some(func) = node_ref.maybe_function() {
                let parent_scope = FuncNodeRef::from_node_ref(node_ref).parent_scope();
                TreeName::new(db, node_ref.file, parent_scope, func.name())
            } else {
                lookup(db.python_state.typing(), "Callable")?
            }
        }
        Type::RecursiveType(_) => todo!(),
        Type::NewType(n) => from_node_ref(NodeRef::from_link(db, n.name_node)),
        Type::ParamSpecArgs(_) => todo!(),
        Type::ParamSpecKwargs(_) => todo!(),
        Type::Literal(l) => {
            let node_ref = l.fallback_node_ref(db);
            TreeName::new(
                db,
                node_ref.file,
                ParentScope::Module,
                node_ref.node().name(),
            )
        }
        Type::Dataclass(_) => todo!(),
        Type::TypedDict(_td) => todo!(),
        Type::NamedTuple(_) => todo!(),
        Type::Enum(_) => todo!(),
        Type::EnumMember(_) => todo!(),
        Type::Module(file_index) => {
            return Some(NameLike::ModuleName(ModuleName {
                db,
                file: db.loaded_python_file(*file_index),
            }))
        }
        Type::Namespace(_) => todo!(),
        Type::Super { class, .. } => {
            // TODO this only cares about one class, when it could care about all bases
            for base in class.class(db).bases(db) {
                if let TypeOrClass::Class(base) = base {
                    return type_to_name(i_s, file, &base.as_type(db));
                }
            }
            return None;
        }
        Type::CustomBehavior(_) => todo!(),
        Type::DataclassTransformObj(_) => todo!(),
        Type::Self_ => {
            if let Some(cls) = i_s.current_class() {
                return type_to_name(i_s, file, &cls.as_type(db));
            } else {
                recoverable_error!("Could not find the current class for Self");
                return None;
            }
        }
        Type::Union(_) | Type::Never(_) => {
            // This probably only happens for Type[int | str], which should probably be handled
            // separately.
            return None;
        }
    }))
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
