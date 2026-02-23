/*
 * Inference is a module for completions, goto, etc. This needs additional inference and not just
 * standard type checking. Type checking should always be done first.
 * */

use std::{borrow::Cow, cell::Cell, sync::Arc};

use parsa_python_cst::{
    Atom, DefiningStmt, DottedAsNameContent, DottedImportName, FunctionDef, GotoNode,
    Name as CSTName, NameDefParent, NameImportParent, NameParent, NodeIndex, Primary,
    PrimaryContent, PrimaryOrAtom, PrimaryTarget, PrimaryTargetOrAtom, Scope, TypeLike,
};
use utils::FastHashSet;
use vfs::{DirectoryEntry, Entries, FileEntry, FileIndex};

use crate::{
    InputPosition, ValueName,
    completion::ScopesIterator,
    database::{Database, ParentScope, PointKind, Specific},
    debug,
    file::{
        ClassInitializer, ClassNodeRef, File, FuncNodeRef, PythonFile,
        expect_class_or_simple_generic, first_defined_name,
    },
    format_data::FormatData,
    inference_state::{InferenceState, Mode},
    inferred::Inferred,
    matching::LookupKind,
    name::{ModuleName, Name, NodeName, Range, TreeName},
    node_ref::NodeRef,
    pytest::find_pytest_fixture_for_param,
    recoverable_error,
    result_context::ResultContext,
    type_::{LookupResult, Type, TypeVarLikeName, TypeVarName, UnionType},
    type_helpers::{Function, TypeOrClass},
    utils::is_file_with_python_ending,
};

pub(crate) struct PositionalDocument<'db, T> {
    pub db: &'db Database,
    pub file: &'db PythonFile,
    pub scope: Scope<'db>,
    pub node: T,
}

impl<T> Clone for PositionalDocument<'_, T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            db: self.db,
            file: self.file,
            scope: self.scope,
            node: self.node.clone(),
        }
    }
}
impl<T> Copy for PositionalDocument<'_, T> where T: Copy {}

impl<'db> PositionalDocument<'db, GotoNode<'db>> {
    pub fn for_goto(
        db: &'db Database,
        file: &'db PythonFile,
        pos: InputPosition,
    ) -> anyhow::Result<Self> {
        let position = file.line_column_to_byte(pos)?;
        let (scope, node) = file.tree.goto_node(position.byte);
        if std::cfg!(debug_assertions) && !matches!(pos, InputPosition::NthUTF8Byte(_)) {
            debug!(
                "Position for goto-like operation {}->{pos:?} on leaf {node:?} in scope {:?}",
                file.file_path(db),
                scope.short_debug_info()
            );
        }
        let result = file.ensure_calculated_diagnostics(db);
        debug_assert!(result.is_ok());
        Ok(Self {
            db,
            file,
            scope,
            node,
        })
    }

    fn lookup_without_errors(
        &self,
        i_s: &InferenceState,
        t: &Type,
        name: &str,
        kind: LookupKind,
    ) -> LookupResult {
        t.lookup(
            i_s,
            self.file,
            name,
            kind,
            &mut ResultContext::Unknown,
            &|_issue| (),
            &|_t_of_attr_error| (),
        )
    }

    fn infer_position(&self) -> Option<Inferred> {
        let result = match &self.node {
            GotoNode::Name(name) => self.infer_name(*name),
            GotoNode::ImportFromAsName { import_as_name, .. } => {
                self.infer_name(import_as_name.name_def().name())
            }
            GotoNode::Primary(primary) => Some(self.infer_primary(*primary)),
            GotoNode::PrimaryTarget(target) => self.infer_primary_target(*target),
            GotoNode::Operator {
                first,
                magic_method,
                ..
            } => self.with_i_s(|i_s| {
                self.lookup_without_errors(
                    i_s,
                    &self
                        .file
                        .inference(i_s)
                        .infer_expression_part(*first)
                        .as_cow_type(i_s),
                    magic_method,
                    LookupKind::OnlyType,
                )
                .into_maybe_inferred()
            }),
            GotoNode::AugAssignOperator {
                target,
                inplace_magic_method,
                normal_magic_method,
                ..
            } => self.with_i_s(|i_s| {
                let lookup = |method| {
                    self.lookup_without_errors(
                        i_s,
                        &self
                            .file
                            .inference(i_s)
                            .infer_target(target.clone(), true)?
                            .as_cow_type(i_s),
                        method,
                        LookupKind::OnlyType,
                    )
                    .into_maybe_inferred()
                };
                lookup(inplace_magic_method).or_else(|| lookup(normal_magic_method))
            }),
            GotoNode::Atom(atom) => Some(self.infer_atom(*atom)),
            GotoNode::GlobalName(name_def) | GotoNode::NonlocalName(name_def) => {
                self.infer_name(name_def.name())
            }
            GotoNode::None => None,
        };
        if let Some(result) = &result
            && let Some(node_ref) = result.maybe_saved_node_ref(self.db)
            && node_ref.point().maybe_calculated_and_specific() == Some(Specific::SimpleGeneric)
        {
            return Some(Inferred::from_type(
                expect_class_or_simple_generic(self.db, node_ref).into_owned(),
            ));
        }
        result
    }
}

impl<'db, T> PositionalDocument<'db, T> {
    pub fn with_i_s<R>(&self, callback: impl FnOnce(&InferenceState) -> R) -> R {
        with_i_s_non_self(self.db, self.file, self.scope, callback)
    }

    pub fn infer_name(&self, name: CSTName) -> Option<Inferred> {
        match name.parent() {
            NameParent::NameDef(name_def) => self
                .maybe_inferred_node_index(name_def.index())
                .or_else(|| {
                    if let DefiningStmt::Walrus(walrus) = name_def.expect_defining_stmt() {
                        Some(self.with_i_s(|i_s| {
                            self.file
                                .inference(i_s)
                                .infer_expression(walrus.expression())
                        }))
                    } else {
                        None
                    }
                }),
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
                .infer_atom(atom, &mut ResultContext::ValueExpected)
        })
    }

    fn maybe_inferred_node_index(&self, node_index: NodeIndex) -> Option<Inferred> {
        let n = NodeRef::new(self.file, node_index);
        self.with_i_s(|i_s| {
            let result = n.maybe_inferred(i_s);
            if let Some(result) = &result
                && let Some(saved) = result.maybe_saved_node_ref(self.db)
                && matches!(
                    saved.point().maybe_specific(),
                    Some(Specific::OverloadUnreachable)
                )
            {
                let n = Function::new_with_unknown_parent(self.db, saved)
                    .original_func_for_overload()?;
                return n.maybe_inferred(i_s);
            }
            result
        })
    }

    pub fn infer_primary(&self, primary: Primary) -> Inferred {
        self.with_i_s(|i_s| {
            self.file
                .inference(i_s)
                .infer_primary(primary, &mut ResultContext::Unknown)
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
                    .cache_import_dotted_name(i_s.db, dotted, import_result)
            })
        }
        if let Some(import_result) = import_result {
            import_result.into_inferred(self.db)
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

    pub fn infer_primary_target_or_atom(&self, p_or_a: PrimaryTargetOrAtom) -> Option<Inferred> {
        match p_or_a {
            PrimaryTargetOrAtom::PrimaryTarget(p) => self.infer_primary_target(p),
            PrimaryTargetOrAtom::Atom(a) => Some(self.infer_atom(a)),
        }
    }

    fn infer_primary_target(&self, target: PrimaryTarget) -> Option<Inferred> {
        self.with_i_s(|i_s| self.file.inference(i_s).infer_primary_target(target, false))
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
        Scope::Function(f) => {
            ensure_cached_func(db, file, f);
            ParentScope::Function(f.index())
        }
        Scope::Class(c) => ParentScope::Class(c.index()),
        Scope::Lambda(lambda) => {
            return with_i_s_non_self(db, file, lambda.parent_scope(), callback);
        }
    };
    InferenceState::run_with_parent_scope(db, file, parent_scope, |i_s| {
        callback(&i_s.with_mode(Mode::AvoidErrors { had_error }))
    })
}

fn ensure_cached_func(db: &Database, file: &PythonFile, f: FunctionDef) {
    with_i_s_non_self(db, file, f.parent_scope(), |i_s| {
        let func = Function::new_with_unknown_parent(db, NodeRef::new(file, f.index()));
        func.ensure_cached_func(i_s);
    });
}

#[derive(Copy, Clone, Debug)]
pub enum ReferencesGoal {
    OnlyCurrentFile,
    // This will still include definitions within dependencies
    OnlyTypeCheckedWorkspaces,
    AllFilesIncludingDependencies,
}

#[derive(Copy, Clone, Debug)]
pub enum GotoGoal {
    PreferStubs,
    PreferNonStubs,
    Indifferent,
}

pub(crate) struct GotoResolver<'db, C> {
    pub infos: PositionalDocument<'db, GotoNode<'db>>,
    goal: GotoGoal,
    on_result: C,
}

impl<'db, C> GotoResolver<'db, C> {
    pub fn new(
        infos: PositionalDocument<'db, GotoNode<'db>>,
        goal: GotoGoal,
        on_result: C,
    ) -> Self {
        Self {
            infos,
            goal,
            on_result,
        }
    }

    pub fn on_node_range(&self) -> Option<Range<'db>> {
        let node_index = match self.infos.node {
            GotoNode::Name(name) => name.index(),
            GotoNode::ImportFromAsName { on_name, .. } => on_name.index(),
            GotoNode::Primary(primary) => primary.index(),
            GotoNode::PrimaryTarget(primary_target) => primary_target.index(),
            GotoNode::Operator { operator, .. } | GotoNode::AugAssignOperator { operator, .. } => {
                operator.index()
            }
            GotoNode::GlobalName(name_def) | GotoNode::NonlocalName(name_def) => name_def.index(),
            GotoNode::Atom(atom) => atom.index(),
            GotoNode::None => return None,
        };
        let file = self.infos.file;
        let start = file.tree.node_start_position(node_index);
        let end = file.tree.node_end_position(node_index);
        Some((
            file.byte_to_position_infos(self.infos.db, start),
            file.byte_to_position_infos(self.infos.db, end),
        ))
    }
}

impl<'db, C: for<'a> FnMut(Name<'db, 'a>) -> T, T> GotoResolver<'db, C> {
    // TODO it seems like type inference is wrong at some point in Rust and we have to help it a
    // bit.
    fn new2(infos: PositionalDocument<'db, GotoNode<'db>>, goal: GotoGoal, on_result: C) -> Self {
        Self {
            infos,
            goal,
            on_result,
        }
    }

    pub fn goto(mut self, follow_imports: bool) -> Vec<T> {
        if let Some(names) = self.goto_name(follow_imports, true) {
            return names;
        }
        let mut callback = self.on_result;
        GotoResolver {
            infos: self.infos,
            goal: self.goal,
            on_result: &mut |n: ValueName<'db, '_>| callback(n.name),
        }
        .infer_definition()
        .1
    }

    fn calculate_return(&mut self, name: Name<'db, '_>) -> T {
        let name = goto_with_goal(name, self.goal);
        (self.on_result)(name)
    }

    fn goto_on_file(&mut self, file_index: FileIndex) -> T {
        let db = self.infos.db;
        let file = db.loaded_python_file(file_index);
        self.calculate_return(Name::ModuleName(ModuleName { db, file }))
    }

    fn try_to_follow(&mut self, n: NodeRef<'db>, follow_imports: bool) -> Option<T> {
        self.process_follow_import_result(try_to_follow(self.infos.db, n, follow_imports)?)
    }

    fn process_follow_import_result(&mut self, r: Option<FollowImportResult<'db>>) -> Option<T> {
        Some(match r? {
            FollowImportResult::File(file_index) => self.goto_on_file(file_index),
            FollowImportResult::TreeName(n) => self.calculate_return(Name::TreeName(n)),
        })
    }

    fn check_node_ref_and_maybe_follow_import(
        &mut self,
        node_ref: NodeRef<'db>,
        follow_imports: bool,
    ) -> Option<T> {
        self.process_follow_import_result(check_node_ref_and_maybe_follow_import(
            self.infos.db,
            node_ref,
            follow_imports,
        ))
    }

    fn goto_name(&mut self, follow_imports: bool, check_inferred_attrs: bool) -> Option<Vec<T>> {
        let db = self.infos.db;
        let file = self.infos.file;
        let node = self.infos.node.clone();
        let mut lookup_on_name = |name: CSTName| {
            let p = file.points.get(name.index());
            if p.calculated() {
                match p.kind() {
                    PointKind::Redirect => {
                        let node_ref = p.as_redirected_node_ref(db);
                        return self
                            .check_node_ref_and_maybe_follow_import(node_ref, follow_imports)
                            .map(|r| vec![r]);
                    }
                    PointKind::Specific => {
                        if matches!(
                            p.specific(),
                            Specific::NameOfNameDef | Specific::FirstNameOfNameDef
                        ) {
                            let name_def = name.name_def().unwrap();
                            match name_def.expect_type() {
                                TypeLike::ParamName(_) => {
                                    let (func_name, decorated) =
                                        name_def.func_param_including_error_recovery();
                                    if let Some(fixture) = find_pytest_fixture_for_param(
                                        db, file, name_def, func_name, decorated,
                                    ) {
                                        return Some(vec![self.calculate_return(Name::TreeName(
                                            TreeName::new(
                                                db,
                                                fixture.file,
                                                Scope::Module,
                                                fixture.node().name(),
                                            ),
                                        ))]);
                                    }
                                }
                                TypeLike::DottedAsName(_) => {
                                    let file_index = self.infos.infer_name(name)?.maybe_file(db)?;
                                    return Some(vec![self.goto_on_file(file_index)]);
                                }
                                TypeLike::ImportFromAsName(_) => return None,
                                _ => (),
                            }
                            let first = first_defined_name(file, name.index());
                            return self
                                .check_node_ref_and_maybe_follow_import(
                                    NodeRef::new(file, first),
                                    follow_imports,
                                )
                                .map(|r| vec![r]);
                        }
                    }
                    PointKind::FileReference => {
                        return Some(vec![self.calculate_return(Name::ModuleName(ModuleName {
                            db,
                            file: db.loaded_python_file(p.file_index()),
                        }))]);
                    }
                    _ => (),
                }
            } else if let NameParent::DottedImportName(_) = name.parent() {
                // TODO shouldn't this be pre-calculated?
                let file_index = self.infos.infer_name(name)?.maybe_file(db)?;
                return Some(vec![self.goto_on_file(file_index)]);
            }
            None
        };
        match node {
            GotoNode::Name(name) => lookup_on_name(name),
            GotoNode::Primary(primary) => match primary.second() {
                PrimaryContent::Attribute(name) => lookup_on_name(name).or_else(|| {
                    let base = self.infos.infer_primary_or_atom(primary.first());
                    self.goto_primary_attr(
                        base,
                        name.as_code(),
                        follow_imports,
                        check_inferred_attrs,
                    )
                }),
                _ => None,
            },
            GotoNode::PrimaryTarget(target) => match target.second() {
                PrimaryContent::Attribute(name) => {
                    let inf = self.infos.infer_primary_target_or_atom(target.first())?;
                    self.goto_primary_attr(
                        inf,
                        name.as_code(),
                        follow_imports,
                        check_inferred_attrs,
                    )
                }
                _ => None,
            },
            GotoNode::ImportFromAsName { import_as_name, .. } => Some(vec![self.try_to_follow(
                NodeRef::new(file, import_as_name.name_def().index()),
                follow_imports,
            )?]),
            GotoNode::GlobalName(name_def) | GotoNode::NonlocalName(name_def) => {
                let ref_ = NodeRef::new(file, name_def.index()).global_or_nonlocal_ref();
                if let Some(result) = self.try_to_follow(ref_, follow_imports) {
                    Some(vec![result])
                } else {
                    // This essentially just returns the name of the global definition, because we
                    // could not goto the original.
                    Some(vec![self.calculate_return(Name::TreeName(TreeName::new(
                        db,
                        file,
                        self.infos.scope,
                        name_def.name(),
                    )))])
                }
            }
            GotoNode::Operator { .. }
            | GotoNode::AugAssignOperator { .. }
            | GotoNode::Atom(_)
            | GotoNode::None => None,
        }
    }
    fn goto_primary_attr(
        &mut self,
        base: Inferred,
        name: &str,
        follow_imports: bool,
        check_inferred_attrs: bool,
    ) -> Option<Vec<T>> {
        let mut results = vec![];
        let db = self.infos.db;
        with_i_s_non_self(db, self.infos.file, self.infos.scope, |i_s| {
            for t in unpack_union_types(db, base.as_cow_type(i_s)).iter_with_unpacked_unions(db) {
                let lookup = self
                    .infos
                    .lookup_without_errors(i_s, t, name, LookupKind::Normal);
                match lookup {
                    LookupResult::GotoName { name, .. } => {
                        if let Some(result) = self.check_node_ref_and_maybe_follow_import(
                            NodeRef::from_link(db, name),
                            follow_imports,
                        ) {
                            results.push(result);
                            continue;
                        }
                    }
                    LookupResult::FileReference(file_index) => {
                        results.push(self.goto_on_file(file_index));
                        continue;
                    }
                    _ => (),
                }
                if check_inferred_attrs && let Some(inf) = lookup.into_maybe_inferred() {
                    let t = inf.as_cow_type(i_s);
                    type_to_name(i_s, &t, &mut |name| {
                        let name = goto_with_goal(name, self.goal);
                        results.push((self.on_result)(name))
                    })
                }
            }
        });
        (!results.is_empty()).then_some(results)
    }
}

pub(crate) fn try_to_follow_imports<'db>(
    db: &'db Database,
    file: &'db PythonFile,
    n: CSTName,
) -> Option<FollowImportResult<'db>> {
    let name_def = n.name_def()?;
    match name_def.maybe_import() {
        Some(NameImportParent::ImportFromAsName(_)) => {
            let ref_ = NodeRef::new(file, name_def.index());
            if let Some(result) = try_to_follow(db, ref_, true) {
                return result;
            }
        }
        Some(NameImportParent::DottedAsName(_)) => {
            let p = NodeRef::new(file, name_def.index()).point();
            if p.kind() == PointKind::FileReference {
                return Some(FollowImportResult::File(p.file_index()));
            }
        }
        None => {
            if matches!(
                name_def.parent(),
                NameDefParent::GlobalStmt | NameDefParent::NonlocalStmt
            ) {
                let ref_ = NodeRef::new(file, name_def.index()).global_or_nonlocal_ref();
                if let Some(result) = try_to_follow(db, ref_, true) {
                    return result;
                }
            }
        }
    }
    None
}

fn try_to_follow<'db>(
    db: &'db Database,
    n: NodeRef<'db>,
    follow_imports: bool,
) -> Option<Option<FollowImportResult<'db>>> {
    let p = n.point();
    if !p.calculated() {
        return None;
    }
    match p.kind() {
        PointKind::Redirect => Some(check_node_ref_and_maybe_follow_import(
            db,
            p.as_redirected_node_ref(db),
            follow_imports,
        )),
        PointKind::FileReference => Some(Some(FollowImportResult::File(p.file_index()))),
        _ => None,
    }
}

fn check_node_ref_and_maybe_follow_import<'db>(
    db: &'db Database,
    node_ref: NodeRef<'db>,
    follow_imports: bool,
) -> Option<FollowImportResult<'db>> {
    let n = node_ref.maybe_name()?;
    if follow_imports && let result @ Some(_) = try_to_follow_imports(db, node_ref.file, n) {
        return result;
    }
    Some(FollowImportResult::TreeName(
        TreeName::with_unknown_parent_scope(db, node_ref.file, n),
    ))
}

pub(crate) enum FollowImportResult<'db> {
    File(FileIndex),
    TreeName(TreeName<'db>),
}

pub(crate) struct ReferencesResolver<'db, C, T> {
    infos: PositionalDocument<'db, GotoNode<'db>>,
    definitions: FastHashSet<(FileIndex, usize)>,
    results: Vec<T>,
    on_result: C,
}

impl<'db, C: FnMut(Name<'db, '_>) -> T, T> ReferencesResolver<'db, C, T> {
    pub fn new(infos: PositionalDocument<'db, GotoNode<'db>>, on_result: C) -> Self {
        Self {
            infos,
            definitions: Default::default(),
            results: Default::default(),
            on_result,
        }
    }

    pub fn references(mut self, goal: ReferencesGoal, include_declarations: bool) -> Vec<T> {
        debug!("Calculate references for {:?}", self.infos.node);
        let Some(on_name) = self.infos.node.on_name() else {
            return vec![];
        };
        let search_name = on_name.as_code();

        let mut is_globally_reachable = false;
        let db = self.infos.db;

        //  1. Find the original definition

        GotoResolver::new2(self.infos.clone(), GotoGoal::Indifferent, |n| {
            follow_goto_if_necessary(n, &mut |name| {
                if !self.definitions.is_empty() {
                    // This is an import, definitions were already added
                    return;
                }

                is_globally_reachable |= match &name {
                    Name::TreeName(tree_name) => {
                        let mut scopes = ScopesIterator {
                            file: name.file(),
                            only_reachable: true,
                            current: Some(tree_name.parent_scope),
                        };
                        !scopes.any(|s| matches!(s, Scope::Function(_) | Scope::Lambda(_)))
                    }
                    _ => true,
                };

                let other = if name.in_stub() {
                    name.goto_non_stub()
                } else {
                    name.goto_stub()
                };
                let should_add_results =
                    include_declarations && !matches!(goal, ReferencesGoal::OnlyCurrentFile);
                if let Some(other) = other {
                    self.definitions.insert(to_unique_position(&other));
                    if should_add_results {
                        self.results.push((self.on_result)(other))
                    }
                }

                self.definitions.insert(to_unique_position(&name));
                if should_add_results
                    || include_declarations && name.file().file_index == self.infos.file.file_index
                {
                    self.results.push((self.on_result)(name));
                }
            });
        })
        .goto_name(false, false);
        if self.definitions.is_empty() {
            if on_name.name_def().is_some() {
                debug!(
                    "Did not find the original reference definition, \
                        but we're using the one below the cursor"
                );
                // On imports that cannot be found goto will not land anywhere, but we still want
                // to perfom reference search even though the imports are not detectable.
                let n = Name::TreeName(TreeName::with_unknown_parent_scope(
                    self.infos.db,
                    self.infos.file,
                    on_name,
                ));
                self.definitions.insert(to_unique_position(&n));
                self.results.push((self.on_result)(n))
            } else {
                debug!("Did not find the original reference definition for {search_name}");
                return vec![];
            }
        }
        debug!(
            "Finding references on {search_name} now for definitions {:?}",
            &self.definitions
        );

        // 2. Find all the references to the original definitions

        match goal {
            _ if !is_globally_reachable => {
                self.find_references_in_file(self.infos.file, search_name)
            }
            ReferencesGoal::OnlyCurrentFile => {
                self.find_references_in_file(self.infos.file, search_name)
            }
            ReferencesGoal::OnlyTypeCheckedWorkspaces => self.find_references_in_workspace_entries(
                db.vfs.workspaces.entries_to_type_check(),
                search_name,
            ),
            ReferencesGoal::AllFilesIncludingDependencies => self
                .find_references_in_workspace_entries(
                    db.vfs.workspaces.iter().map(|x| &x.entries),
                    search_name,
                ),
        }
        self.results
    }

    fn find_references_in_file(&mut self, file: &'db PythonFile, search_name: &str) {
        let result = file.ensure_calculated_diagnostics(self.infos.db);
        debug_assert!(result.is_ok());
        for name in file.tree.filter_all_names(None) {
            if name.as_code() == search_name {
                let mut add_all_names = false;
                GotoResolver::new(
                    PositionalDocument::for_goto(
                        self.infos.db,
                        file,
                        InputPosition::NthUTF8Byte(name.start() as usize),
                    )
                    .unwrap(),
                    GotoGoal::Indifferent,
                    |n: Name| {
                        follow_goto_if_necessary(n, &mut |n| {
                            if self.definitions.contains(&to_unique_position(&n)) {
                                add_all_names = true;
                            }
                        })
                    },
                )
                .goto_name(false, false);
                if add_all_names {
                    let n = Name::TreeName(TreeName::with_unknown_parent_scope(
                        self.infos.db,
                        file,
                        name,
                    ));
                    if !self.definitions.contains(&to_unique_position(&n)) {
                        self.results.push((self.on_result)(n));
                    }
                }
            }
        }
    }

    fn find_references_in_workspace_entries<'x>(
        &mut self,
        workspaces_entries: impl Iterator<Item = &'x Entries>,
        search_name: &str,
    ) {
        let db = self.infos.db;
        let in_name_regex = regex::Regex::new(&format!(r"\b{search_name}\b")).unwrap();
        let mut files = vec![];
        let mut maybe_check_file = |file_entry: &Arc<FileEntry>| {
            if let Some(file_index) = db.vfs.ensure_file_for_file_entry_with_conditional(
                file_entry.clone(),
                false,
                |code| in_name_regex.is_match(code),
                |file_index, code| {
                    PythonFile::from_file_entry_and_code(&db.project, file_index, file_entry, code)
                },
            ) {
                files.push(db.loaded_python_file(file_index));
            }
        };
        for entries in workspaces_entries {
            entries.walk_entries(&db.vfs, &mut |_, dir_entry| {
                if let DirectoryEntry::File(file) = dir_entry
                    && (is_file_with_python_ending(&file.name)
                        // We only want to check Python files, but loaded notebooks sometimes have
                        // different endings.
                        || file.get_file_index().is_some())
                {
                    maybe_check_file(file)
                }
                true
            });
        }
        for file in files {
            self.find_references_in_file(file, search_name);
        }
    }
}

fn to_unique_position(n: &Name) -> (FileIndex, usize) {
    (n.file().file_index, n.name_range().0.byte_position)
}

fn follow_goto_if_necessary<'db, 'x>(name: Name<'db, '_>, on_name: &mut impl FnMut(Name<'db, '_>)) {
    let mut check_name = |tree_name: &TreeName<'db>, start| {
        GotoResolver::new(
            PositionalDocument::for_goto(
                tree_name.db,
                tree_name.file,
                InputPosition::NthUTF8Byte(start as usize),
            )
            .unwrap(),
            GotoGoal::Indifferent,
            |n: Name<'db, '_>| follow_goto_if_necessary(n, on_name),
        )
        .goto_name(false, false);
    };
    if let Name::TreeName(tree_name) = &name
        && let Some(name_def) = tree_name.cst_name.name_def()
    {
        match name_def.maybe_import() {
            Some(NameImportParent::ImportFromAsName(as_name)) => {
                // Follow only if it is a
                //
                //     from ... import foo as foo
                //     or
                //     from ... import foo
                //
                let (name, name_def) = as_name.unpack();
                if name_def.as_code() == name.as_code() {
                    check_name(tree_name, name_def.start())
                }
            }
            Some(NameImportParent::DottedAsName(dotted)) => match dotted.unpack() {
                DottedAsNameContent::Simple(name_def, _) => check_name(tree_name, name_def.start()),
                DottedAsNameContent::WithAs(dotted_import_name, name_def) => {
                    // Follow only if it is import foo as foo (maybe used in stubs to reexport)
                    if name_def.as_code() == dotted_import_name.as_code() {
                        check_name(tree_name, name_def.start())
                    }
                }
            },
            None => match name_def.parent() {
                NameDefParent::GlobalStmt | NameDefParent::NonlocalStmt => {
                    check_name(tree_name, name_def.start());
                }
                _ => (),
            },
        }
    }
    on_name(name)
}

impl<'db, C: for<'a> FnMut(ValueName<'db, 'a>) -> T, T> GotoResolver<'db, C> {
    pub fn infer_definition(&mut self) -> (Inferred, Vec<T>) {
        let mut result = vec![];
        let Some(inf) = self.infos.infer_position() else {
            return (Inferred::new_any_from_error(), result);
        };
        let file = self.infos.file;
        let db = self.infos.db;
        let scope = self.infos.scope;
        with_i_s_non_self(db, file, scope, |i_s| {
            for type_ in inf.as_cow_type(i_s).iter_with_unpacked_unions(db) {
                debug!(
                    "Part of inferring type definition: {:?}",
                    type_.format_short(db)
                );
                type_to_name(i_s, type_, &mut |name| {
                    let name = goto_with_goal(name, self.goal);
                    let callback = &mut self.on_result;
                    result.push(callback(ValueName { name, type_ }))
                })
            }
        });
        (inf, result)
    }
}

fn goto_with_goal<'db, 'x>(name: Name<'db, 'x>, goal: GotoGoal) -> Name<'db, 'x> {
    match goal {
        GotoGoal::PreferStubs => name.goto_stub().unwrap_or(name),
        GotoGoal::PreferNonStubs => name.goto_non_stub().unwrap_or(name),
        GotoGoal::Indifferent => name,
    }
}

fn type_to_name<'db>(i_s: &InferenceState<'db, '_>, t: &Type, add: &mut impl FnMut(Name<'db, '_>)) {
    let db = i_s.db;
    let from_node_ref = |node_ref: NodeRef<'db>| {
        Name::TreeName(TreeName::with_unknown_parent_scope(
            db,
            node_ref.file,
            node_ref.expect_name(),
        ))
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
        Name::TreeName(TreeName::with_parent_scope(
            db,
            node_ref.file,
            parent_scope,
            node_ref.node().name(),
        ))
    };
    let lookup = |module: &'db PythonFile, name| Some(from_node_ref(module.lookup_symbol(name)?));
    match t {
        Type::Class(c) => add(from_class_node_ref(c.node_ref(db))),
        Type::None => {
            if let Some(n) = lookup(db.python_state.types(), "NoneType") {
                add(n)
            }
        }
        Type::Tuple(tup) => {
            let node_ref = tup.class(db).node_ref.to_db_lifetime(db);
            add(Name::TreeName(TreeName::new(
                db,
                node_ref.file,
                Scope::Module,
                node_ref.node().name(),
            )))
        }
        Type::Any(_) => (),
        Type::Intersection(intersection) => {
            for t in intersection.iter_entries() {
                type_to_name(i_s, t, add);
            }
        }
        Type::FunctionOverload(overload) => {
            let first = overload.iter_functions().next().unwrap();
            type_to_name(i_s, &Type::Callable(first.clone()), add)
        }
        Type::TypeVar(tv) => match tv.type_var.name {
            TypeVarName::Name(tvl_name) => add(from_type_var_like_name(tvl_name)),
            TypeVarName::Self_ | TypeVarName::UntypedParam { .. } => (),
        },
        Type::Type(t) => type_to_name(i_s, t, add),
        Type::Callable(callable) => {
            let node_ref = NodeRef::from_link(db, callable.defined_at);
            if let Some(func) = node_ref.maybe_function() {
                add(Name::TreeName(TreeName::with_parent_scope(
                    db,
                    node_ref.file,
                    FuncNodeRef::from_node_ref(node_ref).parent_scope(),
                    func.name(),
                )))
            } else if let Some(callable) = lookup(db.python_state.typing(), "Callable") {
                add(callable)
            }
        }
        Type::RecursiveType(rec) => type_to_name(i_s, rec.calculated_type(db), add),
        Type::NewType(n) => add(from_node_ref(NodeRef::from_link(db, n.name_node))),
        Type::ParamSpecArgs(usage) | Type::ParamSpecKwargs(usage) => {
            add(from_type_var_like_name(usage.param_spec.name))
        }
        Type::Literal(l) => {
            let node_ref = l.fallback_node_ref(db);
            add(Name::TreeName(TreeName::with_parent_scope(
                db,
                node_ref.file,
                node_ref.class_storage().parent_scope,
                node_ref.node().name(),
            )))
        }
        Type::Dataclass(dataclass) => add(from_class_node_ref(dataclass.class.node_ref(db))),
        // It seems like dataclass transform is only used as an internal type
        Type::DataclassTransformObj(_) => (),
        Type::TypedDict(td) => {
            let node_ref = NodeRef::from_link(db, td.defined_at);
            if node_ref.maybe_class().is_some() {
                add(from_class_node_ref(ClassNodeRef::from_node_ref(node_ref)))
            } else {
                add(Name::NodeName(NodeName::new(
                    db,
                    node_ref,
                    &td.name_or_fallback(&FormatData::new_short(db)),
                )))
            }
        }
        Type::NamedTuple(nt) => add(Name::NodeName(NodeName::new(
            db,
            NodeRef::from_link(db, nt.__new__.defined_at),
            nt.name(db),
        ))),
        Type::Enum(enum_) => {
            if enum_.is_from_functional_definition(db) {
                add(Name::NodeName(NodeName::new(
                    db,
                    NodeRef::from_link(db, enum_.defined_at),
                    enum_.name.as_str(db),
                )))
            } else {
                add(from_class_node_ref(*enum_.class(db)))
            }
        }
        Type::EnumMember(member) => {
            if let Some(node_ref) = member.name_node(db) {
                add(from_node_ref(node_ref))
            } else {
                // If we have no name we just goto the enum.
                type_to_name(i_s, &Type::Enum(member.enum_.clone()), add)
            }
        }
        Type::Module(file_index) => add(Name::ModuleName(ModuleName {
            db,
            file: db.loaded_python_file(*file_index),
        })),
        Type::Namespace(_) => {
            // Namespaces cannot be used in goto
        }
        Type::Super { class, .. } => {
            // TODO this only cares about one class, when it could care about all bases
            for base in class.class(db).bases(db) {
                if let TypeOrClass::Class(base) = base {
                    type_to_name(i_s, &base.as_type(db), add)
                }
            }
        }
        Type::CustomBehavior(_) => {
            debug!("TODO implement goto for custom behavior");
        }
        Type::Self_ => {
            if let Some(t) = i_s.current_type() {
                type_to_name(i_s, &t, add)
            } else {
                recoverable_error!("Could not find the current class for Self");
            }
        }
        Type::Union(union) => {
            // This shouldn't typically be reached, because we iterate over unions above
            for t in union.iter() {
                type_to_name(i_s, t, add)
            }
        }
        Type::LiteralString { .. } => {
            let node_ref = db.python_state.str_node_ref();
            add(Name::TreeName(TreeName::with_parent_scope(
                db,
                node_ref.file,
                node_ref.class_storage().parent_scope,
                node_ref.node().name(),
            )))
        }
        Type::Never(_) => (),
        Type::TypeForm(tf) => type_to_name(i_s, tf, add),
    }
}

pub(crate) fn unpack_union_types<'a>(db: &Database, t: Cow<'a, Type>) -> Cow<'a, Type> {
    if t.iter_with_unpacked_unions(db)
        .any(|t| matches!(t, Type::Type(x) if x.is_union_like(db)))
    {
        return Cow::Owned(Type::Union(UnionType::from_types(
            t.iter_with_unpacked_unions(db).flat_map(|t| {
                let mut unpacked = None;
                let mut non_unpacked = None;
                match t {
                    Type::Type(t) if t.is_union_like(db) => {
                        unpacked = Some(
                            t.iter_with_unpacked_unions(db)
                                .map(|t| Type::Type(Arc::new(t.clone()))),
                        )
                    }
                    _ => non_unpacked = Some(t.clone()),
                };
                unpacked.into_iter().flatten().chain(non_unpacked)
            }),
            true,
        )));
    }
    t
}
