/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use parsa_python_cst::{CodeIndex, GotoNode, Name as CSTName, NameParent};

use crate::{
    database::{Database, ParentScope},
    debug,
    file::{ClassInitializer, File, FuncNodeRef, PythonFile},
    inference_state::InferenceState,
    inferred::Inferred,
    name::{Name, Names, TreeName},
    node_ref::NodeRef,
    type_::Type,
    InputPosition, ValueName,
};

pub(crate) struct PositionalDocument<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    position: CodeIndex,
}

impl<'db> PositionalDocument<'db> {
    pub fn new(db: &'db Database, file: &'db PythonFile, position: InputPosition) -> Self {
        let position = match position {
            InputPosition::NthByte(pos) => pos as u32,
            InputPosition::Utf8Bytes { line, column } => file.line_column_to_byte(line, column),
            InputPosition::Utf16CodeUnits { line: _, column: _ } => todo!(),
            InputPosition::CodePoints { line: _, column: _ } => todo!(),
        };
        Self { db, file, position }
    }

    fn infer_position(&self) -> Option<Inferred> {
        let result = self.file.ensure_calculated_diagnostics(&self.db);
        debug_assert!(result.is_ok());
        let leaf = self.file.tree.goto_node(self.position);
        debug!(
            "Infer for position {}->{:?} on leaf {leaf:?}",
            self.file.file_path(&self.db),
            self.position
        );
        match leaf {
            GotoNode::Name(name) => Some(infer_name(self.db, self.file, name)),
            GotoNode::Primary(primary) => {
                // TODO don't just use it on expr
                let n = NodeRef::new(self.file, primary.index() - 1);
                n.maybe_inferred(&InferenceState::new(self.db, self.file))
            }
            GotoNode::None => None,
        }
    }

    /*
    fn infer_operator_leaf(&self, _db: &Database, _leaf: Keyword) -> Inferred {
        /*
        if ["(", "[", "{", ")", "]", "}"]
            .iter()
            .any(|&x| x == leaf.as_str())
        {
            if let Some(primary) = leaf.maybe_primary_parent() {
                let i_s = InferenceState::new(db);
                return self
                    .inference(&i_s)
                    .infer_primary(primary, &mut ResultContext::Unknown);
            }
        }
        */
        unimplemented!()
    }

    pub fn infer_definition(&self) -> impl Iterator<Item = T> {
        /*
        let i_s = InferenceState::new(self.db);
        self.file
            .inference(&i_s)
            .infer_name_of_definition(self.cst_name);
        */
        match NameOrKeywordLookup::from_position(&self.file.tree, self.position) {
            NameOrKeywordLookup::Name(name) => TreeName::new(self.db, self.file, name).infer(),
            NameOrKeywordLookup::Keyword(_) => return vec![],
            NameOrKeywordLookup::None => return vec![],
        }
    }
    */

    pub fn complete(&self) -> Names {
        unimplemented!()
    }
}

pub(crate) struct GotoResolver<'db, C> {
    infos: PositionalDocument<'db>,
    on_result: C,
}

impl<'db, C> GotoResolver<'db, C> {
    pub(crate) fn new(infos: PositionalDocument<'db>, on_result: C) -> Self {
        Self { infos, on_result }
    }
}

impl<'db, C: for<'a> Fn(&dyn Name) -> T + Copy + 'db, T> GotoResolver<'db, C> {
    pub fn goto(&self, follow_imports: bool) -> impl Iterator<Item = T> {
        let callback = self.on_result;
        std::iter::empty().map(move |n| callback(n))
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
                name: &type_to_name(db, file, &e.type_)?,
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

fn type_to_name<'db>(db: &'db Database, file: &'db PythonFile, t: &Type) -> Option<TreeName<'db>> {
    let from_node_ref = |node_ref: NodeRef<'db>| {
        TreeName::new(
            db,
            node_ref.file,
            ParentScope::Module,
            node_ref.expect_name(),
        )
    };
    let lookup = |module: &'db PythonFile, name| Some(from_node_ref(module.lookup_symbol(name)?));
    Some(match t {
        Type::Class(c) => {
            let node_ref = c.node_ref(db);
            let parent_scope = ClassInitializer::from_node_ref(node_ref)
                .class_storage
                .parent_scope;
            TreeName::new(db, file, parent_scope, node_ref.node().name())
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
        Type::TypeVar(tv) => {
            // TODO
            return None;
        }
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
        Type::NewType(n) => {
            // TODO
            return None;
        }
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
    })
}

fn infer_name(db: &Database, file: &PythonFile, name: CSTName) -> Inferred {
    let i_s = &InferenceState::new(db, file);
    match name.parent() {
        NameParent::NameDef(_) => todo!(),
        NameParent::Atom(atom) => {
            let n = NodeRef::new(file, atom.index());
            if let Some(inf) = n.maybe_inferred(i_s) {
                return inf;
            }
        }
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
    Inferred::new_never(crate::type_::NeverCause::Other) // TODO
}
