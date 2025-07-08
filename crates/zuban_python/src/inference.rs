/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use std::{borrow::Cow, cell::Cell, rc::Rc};

use parsa_python_cst::{
    Atom, GotoNode, Name as CSTName, NameParent, Primary, PrimaryContent, PrimaryOrAtom, Scope,
};

use crate::{
    database::{Database, ParentScope, PointKind},
    debug,
    file::{ClassInitializer, File, FuncNodeRef, PythonFile},
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::ResultContext,
    name::{ModuleName, Name, TreeName},
    node_ref::NodeRef,
    type_::{Type, TypeVarLikeName, TypeVarName, UnionType},
    InputPosition, ValueName,
};

pub(crate) struct PositionalDocument<'db, T> {
    pub db: &'db Database,
    pub file: &'db PythonFile,
    pub scope: Scope,
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
            GotoNode::Name(name) => Some(self.infer_name(name)),
            GotoNode::Primary(primary) => Some(self.infer_primary(primary)),
            GotoNode::None => None,
        }
    }
}

impl<'db, T> PositionalDocument<'db, T> {
    pub fn with_i_s<R>(&self, callback: impl FnOnce(&InferenceState) -> R) -> R {
        with_i_s_non_self(self.db, self.file, self.scope, callback)
    }

    fn infer_name(&self, name: CSTName) -> Inferred {
        match name.parent() {
            NameParent::NameDef(_) => todo!(),
            NameParent::Atom(atom) => self.infer_atom(atom),
            NameParent::Primary(_) => todo!(),
            NameParent::PrimaryTarget(_) => todo!(),
            NameParent::Kwarg(_) => todo!(),
            NameParent::KeywordPattern(_) => todo!(),
            NameParent::ImportFromAsName(_) => todo!(),
            NameParent::DottedName(_) => todo!(),
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
        let n = NodeRef::new(self.file, atom.index());
        if let Some(inf) = self.with_i_s(|i_s| n.maybe_inferred(i_s)) {
            return inf;
        }
        Inferred::new_never(crate::type_::NeverCause::Other) // TODO?
    }

    pub fn infer_primary(&self, primary: Primary) -> Inferred {
        self.with_i_s(|i_s| {
            self.file
                .inference(i_s)
                .infer_primary(primary, &mut ResultContext::ExpectUnused)
        })
    }

    pub fn infer_primary_or_atom(&self, p_or_a: PrimaryOrAtom) -> Inferred {
        match p_or_a {
            PrimaryOrAtom::Primary(p) => self.infer_primary(p),
            PrimaryOrAtom::Atom(a) => self.infer_atom(a),
        }
    }
}

pub(crate) fn with_i_s_non_self<R>(
    db: &Database,
    file: &PythonFile,
    scope: Scope,
    callback: impl FnOnce(&InferenceState) -> R,
) -> R {
    let had_error = &Cell::new(false);
    let parent_scope = match scope {
        Scope::Module => ParentScope::Module,
        Scope::Function(index) => ParentScope::Function(index),
        Scope::Class(index) => ParentScope::Class(index),
        Scope::Lambda(_) => todo!(),
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
    pub fn goto<R: FromIterator<T>>(self, follow_imports: bool) -> R {
        if let Some(names) = self.goto_name::<R>() {
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

    fn goto_name<R: FromIterator<T>>(&self) -> Option<R> {
        let lookup_on_name = |name: CSTName| {
            // TODO fix parent_scope
            let db = self.infos.db;
            let file = self.infos.file;
            let p = file.points.get(name.index());
            if p.calculated() && p.kind() == PointKind::Redirect {
                let node_ref = p.as_redirected_node_ref(db);
                if let Some(n) = node_ref.maybe_name() {
                    let tree_name = TreeName::new(db, file, ParentScope::Module, n);
                    return Some(std::iter::once((self.on_result)(&tree_name)).collect());
                }
            }
            None
        };
        match self.infos.node {
            GotoNode::Name(name) => lookup_on_name(name),
            GotoNode::Primary(primary) => match primary.second() {
                PrimaryContent::Attribute(name) => lookup_on_name(name).or_else(|| {
                    let base = self.infos.infer_primary_or_atom(primary.first());
                    // base.lookup(i_s)
                    self.infos.with_i_s(|i_s| {
                        /*
                        unpack_union_types(base.as_cow_type(i_s))
                            .iter_with_unpacked_unions()
                            .map(|t| match t {
                                Type::Type(t) =>
                            })
                        */
                        None
                    })
                }),
                _ => None,
            },
            GotoNode::None => None,
        }
    }
}

impl<'db, C: for<'a> Fn(ValueName) -> T + Copy + 'db, T> GotoResolver<'db, C> {
    pub fn infer_type_definition(&self) -> impl Iterator<Item = T> + 'db {
        let inf = self.infos.infer_position();
        let callback = self.on_result;
        let file = self.infos.file;
        let db = self.infos.db;
        inf.map(|t| {
            t.as_type(&InferenceState::new(db, file))
                .into_iter_with_unpacked_unions(db, true)
        })
        .into_iter()
        .flatten()
        .filter_map(move |e| {
            debug!(
                "Part of inferring type definition: {:?}",
                e.type_.format_short(db)
            );
            Some(callback(ValueName {
                name: type_to_name(db, file, &e.type_)?.as_name(),
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

#[expect(unused)]
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

fn type_to_name<'db>(db: &'db Database, file: &'db PythonFile, t: &Type) -> Option<NameLike<'db>> {
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
        Type::FunctionOverload(_) => todo!(),
        Type::TypeVar(tv) => match tv.type_var.name {
            TypeVarName::Name(tvl_name) => match tvl_name {
                TypeVarLikeName::InString { name_node, .. } => {
                    from_node_ref(NodeRef::from_link(db, name_node))
                }
                TypeVarLikeName::SyntaxNode(_) => todo!(),
            },
            TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => return None,
        },
        Type::Type(t) => return type_to_name(db, file, &t),
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
        Type::TypedDict(_) => todo!(),
        Type::NamedTuple(_) => todo!(),
        Type::Enum(_) => todo!(),
        Type::EnumMember(_) => todo!(),
        Type::Module(_) => todo!(),
        Type::Namespace(_) => todo!(),
        Type::Super { .. } => todo!(),
        Type::CustomBehavior(_) => todo!(),
        Type::DataclassTransformObj(_) => todo!(),
        Type::Self_ => todo!(),
        Type::Union(_) | Type::Never(_) => {
            // This probably only happens for Type[int | str], which should probably be handled
            // separately.
            return None;
        }
    }))
}

pub fn unpack_union_types<'a>(db: &Database, t: Cow<'a, Type>) -> Cow<'a, Type> {
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
