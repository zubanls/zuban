use std::{borrow::Cow, collections::HashSet, sync::Arc};

pub use lsp_types::CompletionItemKind;
use parsa_python_cst::{
    ClassDef, CompletionContext, CompletionNode, FunctionDef, NAME_DEF_TO_NAME_DIFFERENCE, Name,
    NameDef, NodeIndex, RestNode, Scope, is_identifier,
};
use vfs::{Directory, DirectoryEntry, Entries, FileIndex, Parent};

use crate::{
    InputPosition,
    database::{ClassKind, Database, ParentScope, PointKind},
    debug,
    file::{ClassNodeRef, File as _, FuncNodeRef, PythonFile, is_reexport_issue},
    goto::{
        FollowImportResult, PositionalDocument, try_to_follow_imports, unpack_union_types,
        with_i_s_non_self,
    },
    imports::{ImportResult, global_import},
    inference_state::InferenceState,
    inferred::Inferred,
    lines::BytePositionInfos,
    matching::Generics,
    name::{ModuleName, Range, TreeName, process_docstring},
    node_ref::NodeRef,
    params::Param,
    pytest::find_all_possible_pytest_fixtures,
    recoverable_error,
    type_::{
        CallableContent, CallableLike, CallableParam, CallableParams, Enum, EnumMemberDefinition,
        FunctionKind, Namespace, ParamType, Type,
    },
    type_helpers::{Class, Function, TypeOrClass, is_private},
};

struct CompletionInfo<'db> {
    node: CompletionNode<'db>,
    rest: RestNode<'db>,
    cursor_position: BytePositionInfos,
}

impl CompletionInfo<'_> {
    fn fix_for_invalid_columns(mut self) -> Self {
        if self.cursor_position.column_out_of_bounds && !self.rest.as_code().is_empty() {
            self.node = CompletionNode::Global { context: None };
            self.rest.ensure_no_rest();
        }
        self
    }
}
impl<'db> PositionalDocument<'db, CompletionInfo<'db>> {
    pub fn for_completion(
        db: &'db Database,
        file: &'db PythonFile,
        pos: InputPosition,
    ) -> anyhow::Result<Self> {
        let cursor_position = file.line_column_to_byte(pos)?;
        let (scope, node, rest) = file.tree.completion_node(cursor_position.byte);
        let result = file.ensure_calculated_diagnostics(db);
        debug!(
            "Complete on position {}->{pos:?} on leaf {node:?} with rest {:?}",
            file.file_path(db),
            rest.as_code()
        );
        debug_assert!(result.is_ok());
        Ok(Self {
            db,
            file,
            scope,
            node: CompletionInfo {
                node,
                rest,
                cursor_position,
            }
            .fix_for_invalid_columns(),
        })
    }
}

pub(crate) struct CompletionResolver<'db, C, T> {
    infos: PositionalDocument<'db, CompletionInfo<'db>>,
    pub on_result: C,
    items: Vec<(CompletionSortPriority<'db>, T)>,
    added_names: HashSet<Cow<'db, str>>,
    should_start_with_lowercase: Option<String>,
    replace_range: Range<'db>,
}

impl<'db, C: for<'a> Fn(Range, &dyn Completion) -> Option<T>, T> CompletionResolver<'db, C, T> {
    pub fn complete(
        db: &'db Database,
        file: &'db PythonFile,
        position: InputPosition,
        filter_with_name_under_cursor: bool,
        on_result: C,
    ) -> anyhow::Result<Vec<T>> {
        let _panic_context = utils::panic_context::enter(format!(
            "completions for {} position {position:?}",
            file.file_path(db)
        ));
        let infos = PositionalDocument::for_completion(db, file, position)?;
        let replace_range = (
            file.byte_to_position_infos(db, infos.node.rest.start()),
            file.byte_to_position_infos(db, infos.node.cursor_position.byte),
        );
        let mut slf = Self {
            infos,
            on_result,
            items: vec![],
            added_names: Default::default(),
            should_start_with_lowercase: None,
            replace_range,
        };
        if filter_with_name_under_cursor {
            slf.should_start_with_lowercase = Some(slf.infos.node.rest.as_code().to_lowercase());
        }
        slf.fill_items();
        slf.items.sort_by_key(|item| item.0);
        Ok(slf.items.into_iter().map(|(_, item)| item).collect())
    }

    fn fill_items(&mut self) {
        let file = self.infos.file;
        let db = self.infos.db;
        match &self.infos.node.node {
            CompletionNode::Attribute { base } => {
                let inf = self.infos.infer_primary_or_atom(*base);
                self.add_attribute_completions(inf)
            }
            CompletionNode::Global { context } => {
                let reachable_scopes = &mut ScopesIterator {
                    file,
                    only_reachable: true,
                    current: Some(self.infos.scope),
                };
                match context {
                    Some(CompletionContext::PrimaryCall(call)) => {
                        self.add_keyword_param_completions(self.infos.infer_primary_or_atom(*call));
                    }
                    Some(CompletionContext::PrimaryTargetCall(call)) => {
                        if let Some(inf) = self.infos.infer_primary_target_or_atom(*call) {
                            self.add_keyword_param_completions(inf);
                        }
                    }
                    None => (),
                }
                for scope in reachable_scopes {
                    match scope {
                        Scope::Module => self.add_global_module_completions(file),
                        Scope::Class(cls) => {
                            let storage = ClassNodeRef::new(file, cls.index()).class_storage();
                            for (_, node_index) in storage.class_symbol_table.iter() {
                                self.maybe_add_tree_name(
                                    file,
                                    scope,
                                    NameDef::by_index(
                                        &file.tree,
                                        node_index - NAME_DEF_TO_NAME_DIFFERENCE,
                                    ),
                                    true,
                                )
                            }
                            self.add_star_imports_completions(
                                file,
                                cls.index(),
                                &mut Default::default(),
                            )
                        }
                        Scope::Function(func) => {
                            func.on_name_def_in_scope(&mut |name_def| {
                                self.maybe_add_tree_name(file, scope, name_def, false)
                            });
                            self.add_star_imports_completions(
                                file,
                                func.index(),
                                &mut Default::default(),
                            )
                        }
                        Scope::Lambda(lambda) => {
                            for param in lambda.params() {
                                self.maybe_add_tree_name(file, scope, param.name_def(), false)
                            }
                        }
                    };
                }
                self.add_module_completions(db.python_state.builtins())
            }
            CompletionNode::ImportName { path: None } => self.add_global_import_completions(),
            CompletionNode::ImportName {
                path: Some((name_def, rest_path)),
            } => {
                let mut result = global_import(db, file, name_def.as_code());
                if let Some(dotted) = rest_path {
                    self.infos.with_i_s(|i_s| {
                        result = file.cache_import_dotted_name(i_s.db, *dotted, result.take())
                    });
                }
                self.add_import_result_completions(result)
            }
            CompletionNode::ImportFromFirstPart { dots, base } => {
                if *dots <= 0 && base.is_none() {
                    self.add_global_import_completions()
                } else {
                    self.add_import_result_completions(self.infos.with_i_s(|i_s| {
                        self.infos
                            .file
                            .import_from_first_part_calculation_without_loading_file(
                                i_s.db,
                                *dots,
                                *base,
                                |_| false,
                            )
                    }))
                }
            }
            CompletionNode::PrimaryTarget { base } => {
                if let Some(inf) = self.infos.infer_primary_target_or_atom(*base) {
                    self.add_attribute_completions(inf)
                }
            }
            CompletionNode::ImportFromTarget { base, dots } => {
                let inf = self.infos.infer_dotted_import_name(*dots, *base);
                self.add_attribute_completions(inf)
            }
            CompletionNode::AsNewName => (),
            CompletionNode::ParamName {
                decorators,
                func_name,
            } => {
                if let Some(iterator) =
                    find_all_possible_pytest_fixtures(db, file, *func_name, *decorators)
                {
                    for (file, name) in iterator {
                        let n = name.as_code();
                        if !self.maybe_add_cow(Cow::Borrowed(n)) {
                            continue;
                        }
                        let result = (self.on_result)(
                            self.replace_range,
                            &CompletionTreeName {
                                db,
                                file,
                                name,
                                kind: CompletionItemKind::FUNCTION,
                            },
                        );
                        if let Some(result) = result {
                            self.items
                                .push((CompletionSortPriority::Default(n), result))
                        }
                    }
                }
            }
            CompletionNode::NecessaryKeyword(keyword) => {
                let keyword = *keyword;
                let result = (self.on_result)(self.replace_range, &KeywordCompletion { keyword });
                if let Some(result) = result {
                    self.items
                        .push((CompletionSortPriority::Default(keyword), result))
                }
            }
            CompletionNode::AfterDefKeyword => (),
            CompletionNode::AfterClassKeyword => (),
            CompletionNode::InsideString => (),
        }
    }

    fn add_keyword_param_completions(&mut self, inf: Inferred) {
        with_i_s_non_self(self.infos.db, self.infos.file, self.infos.scope, |i_s| {
            let maybe_django_query_method = || {
                let bound = inf.maybe_bound_method()?;
                let base = bound.instance.maybe_class(i_s.db)?;
                if !base.has_django_stubs_base_class(i_s.db) {
                    return None;
                }
                let func_ref = NodeRef::from_link(i_s.db, bound.func_link);
                let func = func_ref.maybe_function()?;
                if matches!(
                    func.name().as_code(),
                    "filter"
                        | "create"
                        | "exclude"
                        | "update"
                        | "get"
                        | "get_or_create"
                        | "update_or_create"
                ) && matches!(func_ref.file.name(i_s.db), "query" | "manager")
                    && matches!(base.generics, Generics::List(..))
                {
                    Some(base.nth_type_argument(i_s.db, 0))
                } else {
                    None
                }
            };

            if let Some(model) = maybe_django_query_method() {
                self.add_keyword_params_for_callable_likes(
                    Type::Type(Arc::new(model)).maybe_callable(i_s),
                )
            } else {
                self.add_keyword_params_for_callable_likes(inf.as_cow_type(i_s).maybe_callable(i_s))
            }
        })
    }

    fn add_keyword_params_for_callable_likes(&mut self, c: Option<CallableLike>) {
        let mut add = |c: &CallableContent| {
            if let CallableParams::Simple(params) = &c.params {
                for param in params.iter() {
                    if matches!(
                        param.type_,
                        ParamType::PositionalOrKeyword(_) | ParamType::KeywordOnly(_)
                    ) {
                        if let Some(name) = param.name(self.infos.db) {
                            let keyword_argument = format!("{name}=");
                            if !self.maybe_add_cow(Cow::Owned(keyword_argument.clone())) {
                                continue;
                            }
                            if let Some(result) = (self.on_result)(
                                self.replace_range,
                                &KeywordArgumentCompletion { keyword_argument },
                            ) {
                                self.items
                                    .push((CompletionSortPriority::KeywordArgument, result))
                            }
                        }
                    }
                }
            }
        };
        match c {
            Some(CallableLike::Callable(c)) => add(&c),
            Some(CallableLike::Overload(o)) => {
                for c in o.iter_functions() {
                    add(c)
                }
            }
            None => (),
        }
    }

    fn add_import_result_completions(&mut self, import_result: Option<ImportResult>) {
        match import_result {
            Some(ImportResult::File(file_index)) => {
                if let Ok(file) = self.infos.db.ensure_file_for_file_index(file_index) {
                    self.add_submodule_completions(file)
                }
            }
            Some(ImportResult::Namespace(namespace)) => self.add_namespace_completions(&namespace),
            None | Some(ImportResult::PyTypedMissing) => (),
        }
    }

    fn add_module_completions(&mut self, file: &'db PythonFile) {
        self.add_specific_module_completions(file, true, false, &mut HashSet::default());
        if let Some(normal_file) = file.normal_file_of_stub_file(self.infos.db) {
            self.add_specific_module_completions(normal_file, true, false, &mut HashSet::default());
        }
        self.add_submodule_completions(file)
    }

    fn add_global_module_completions(&mut self, file: &'db PythonFile) {
        self.add_specific_module_completions(file, false, false, &mut HashSet::default());
        if let Some(super_file) = &file.super_file {
            self.add_global_module_completions(self.infos.db.loaded_python_file(super_file.file))
        }
    }

    fn add_namespace_completions(&mut self, namespace: &Namespace) {
        for dir in namespace.directories.iter() {
            self.directory_entries_completions(Directory::entries(&self.infos.db.vfs, dir))
        }
    }

    fn add_module_type_completions(&mut self) {
        // Theoretically all object dunder methods are also importable, but I think
        // they offer no real value
        self.add_class_symbols_with_check(
            self.infos.db.python_state.module_instance().class,
            false,
            |name| ["__init__", "__getattr__", "__path__"].contains(&name),
        );
    }

    fn add_specific_module_completions(
        &mut self,
        file: &'db PythonFile,
        check_reexports: bool,
        check_dunder_all: bool,
        already_visited: &mut HashSet<FileIndex>,
    ) {
        let db = self.infos.db;
        for (symbol, &node_index) in file.symbol_table.iter() {
            // Stubs sometimes import thing like typing without reexporting it, look at builtins.py
            // for example.
            if check_reexports && is_reexport_issue(db, NodeRef::new(file, node_index)) {
                continue;
            }
            if check_dunder_all && !file.is_name_exported_for_star_import(db, symbol) {
                continue;
            }
            self.maybe_add_tree_name(
                file,
                Scope::Module,
                NameDef::by_index(&file.tree, node_index - NAME_DEF_TO_NAME_DIFFERENCE),
                false,
            )
        }
        if !file.star_imports.is_empty() {
            if !already_visited.insert(file.file_index) {
                // Avoid recursing
                return;
            };
            self.add_star_imports_completions(file, 0, already_visited)
        }
    }

    fn add_star_imports_completions(
        &mut self,
        file: &PythonFile,
        scope: NodeIndex,
        already_visited: &mut HashSet<FileIndex>,
    ) {
        for star_import in file.star_imports.iter() {
            if star_import.scope == scope
                && let Some(f) = file.star_import_file(self.infos.db, star_import)
            {
                self.add_specific_module_completions(f, true, true, already_visited)
            }
        }
    }

    fn add_global_import_completions(&mut self) {
        for workspace in self.infos.db.vfs.workspaces.iter() {
            self.directory_entries_completions(&workspace.entries)
        }
    }

    fn add_submodule_completions(&mut self, file: &'db PythonFile) {
        let db = self.infos.db;
        let (file_entry, is_package) = file.file_entry_and_is_package(db);
        if is_package && let Parent::Directory(dir) = &file_entry.parent {
            let dir = dir.upgrade().unwrap();
            self.directory_entries_completions(Directory::entries(&db.vfs, &dir))
        }
    }

    fn directory_entries_completions(&mut self, entries: &Entries) {
        for entry in &entries.iter() {
            let name: &str = match entry {
                DirectoryEntry::File(f) => {
                    if let Some(stripped_name) = f
                        .name
                        .strip_suffix(".py")
                        .or_else(|| f.name.strip_suffix(".pyi"))
                    {
                        if stripped_name == "__init__" {
                            continue;
                        }
                        stripped_name
                    } else {
                        continue;
                    }
                }
                DirectoryEntry::Directory(dir) => &dir.name,
                _ => continue,
            };
            // Unsafe: The name always lives as long as 'db, because file entries are
            // only cleaned up once this lifetime is released.
            let name: &'db str = unsafe { std::mem::transmute(name) };
            if !self.maybe_add(name) || !is_identifier(name) {
                continue;
            }
            if let Some(result) = (self.on_result)(
                self.replace_range,
                &CompletionDirEntry {
                    db: self.infos.db,
                    name,
                    entry,
                },
            ) {
                self.items
                    .push((CompletionSortPriority::new_symbol(name), result))
            }
        }
    }

    fn add_attribute_completions(&mut self, inf: Inferred) {
        let db = self.infos.db;
        let file = self.infos.file;
        with_i_s_non_self(db, file, self.infos.scope, |i_s| {
            self.add_attribute_completions_for_type(i_s, &inf.as_cow_type(i_s))
        })
    }

    fn add_attribute_completions_for_type(&mut self, i_s: &InferenceState, t: &Type) {
        let db = self.infos.db;
        for t in unpack_union_types(db, Cow::Borrowed(t)).iter_with_unpacked_unions(db) {
            match t {
                Type::Type(t) => self.add_for_mro(i_s, t, false),
                Type::Module(module) => {
                    self.add_module_completions(self.infos.db.loaded_python_file(*module));
                    self.add_module_type_completions()
                }
                Type::Namespace(ns) => {
                    self.add_namespace_completions(ns);
                    self.add_module_type_completions()
                }
                Type::Intersection(intersection) => {
                    for t in intersection.iter_entries() {
                        self.add_attribute_completions_for_type(i_s, t)
                    }
                }
                Type::RecursiveType(rec) => {
                    self.add_attribute_completions_for_type(i_s, rec.calculated_type(db))
                }
                t => self.add_for_mro(i_s, t, true),
            }
        }
    }

    fn add_for_mro(&mut self, i_s: &InferenceState, t: &Type, is_instance: bool) {
        if let Type::Self_ = t {
            if let Some(t) = i_s.current_type() {
                self.add_for_mro(i_s, &t, is_instance)
            } else {
                recoverable_error!("TODO caught Self that is not within a class");
            }
        }
        if let Type::Any(_) = t {
            // I decided to not return any completions here to signal the user a difference between
            // object and Any. This essentially removes all the dunder methods that are present on
            // object.
            return;
        }

        for (_, type_or_class) in t.mro(self.infos.db) {
            self.add_for_type_or_class(type_or_class, is_instance)
        }
    }

    fn add_for_type_or_class(&mut self, type_or_class: TypeOrClass, is_instance: bool) {
        let db = self.infos.db;
        match type_or_class {
            TypeOrClass::Type(t) => match t.as_ref() {
                Type::Super {
                    class,
                    mro_index: _,
                    ..
                } => {
                    // TODO this is not fully correct, because some base classes might have been
                    // skipped with the mro_index
                    for base in class.class(db).bases(db) {
                        self.add_for_type_or_class(base, is_instance)
                    }
                }
                Type::Dataclass(dataclass) => {
                    self.add_class_symbols(dataclass.class(db), is_instance)
                }
                Type::Enum(enum_) => self.add_enum_completions(enum_, is_instance),
                Type::EnumMember(member) => self.add_enum_completions(&member.enum_, is_instance),
                // TypedDicts have no relevant completions, the base class takes care of it
                Type::TypedDict(_) => (),
                Type::NamedTuple(nt) => {
                    for param in nt.params() {
                        let comp = NamedTupleMemberCompletion {
                            db,
                            param,
                            file: nt.__new__.defined_at.file,
                        };
                        if !self.maybe_add_cow(Cow::Owned(comp.label().into())) {
                            continue;
                        }
                        if let Some(result) = (self.on_result)(self.replace_range, &comp) {
                            // TODO fix this name for sorting
                            self.items
                                .push((CompletionSortPriority::Default(""), result))
                        }
                    }
                    let tup_cls = db.python_state.tuple_class_with_generics_to_be_defined();
                    self.add_class_symbols(tup_cls, is_instance)
                }
                _ => {
                    debug!("TODO ignored completions for type {t:?}");
                }
            },
            TypeOrClass::Class(c) => self.add_class_symbols(c, is_instance),
        }
    }

    fn add_class_symbols(&mut self, c: Class, is_instance: bool) {
        self.add_class_symbols_with_check(c, is_instance, |_| false)
    }

    fn add_class_symbols_with_check(
        &mut self,
        c: Class,
        is_instance: bool,
        should_ignore: impl Fn(&str) -> bool,
    ) {
        let file = c.node_ref.to_db_lifetime(self.infos.db).file;
        let storage = c.node_ref.to_db_lifetime(self.infos.db).class_storage();
        let class_node = c.node();
        for (symbol, node_index) in storage.class_symbol_table.iter() {
            if is_private(symbol) || should_ignore(symbol) {
                continue;
            }
            let name_def = NameDef::by_index(&file.tree, node_index - NAME_DEF_TO_NAME_DIFFERENCE);
            self.maybe_add_tree_name(file, Scope::Class(class_node), name_def, true)
        }
        if is_instance {
            for (symbol, &node_index) in storage.self_symbol_table.iter() {
                if !self.maybe_add(symbol) || is_private(symbol) || should_ignore(symbol) {
                    continue;
                }
                if let Some(result) = (self.on_result)(
                    self.replace_range,
                    &CompletionTreeName {
                        db: self.infos.db,
                        file,
                        name: NodeRef::new(file, node_index).expect_name(),
                        kind: CompletionItemKind::FIELD,
                    },
                ) {
                    self.items
                        .push((CompletionSortPriority::new_symbol(symbol), result))
                }
            }
        }
    }

    fn add_enum_completions(&mut self, enum_: &Enum, is_instance: bool) {
        for member in &enum_.members {
            if !self.maybe_add_cow(Cow::Owned(member.name(self.infos.db).into())) {
                continue;
            }
            if let Some(result) = (self.on_result)(
                self.replace_range,
                &EnumMemberCompletion {
                    db: self.infos.db,
                    enum_,
                    member,
                },
            ) {
                self.items
                    .push((CompletionSortPriority::EnumMember, result))
            }
        }
        if !enum_.is_from_functional_definition(self.infos.db) {
            self.add_class_symbols(enum_.class(self.infos.db), is_instance)
        }
    }

    fn maybe_add(&mut self, symbol: &'db str) -> bool {
        self.maybe_add_cow(Cow::Borrowed(symbol))
    }

    fn maybe_add_cow(&mut self, symbol: Cow<'db, str>) -> bool {
        if let Some(starts_with) = &self.should_start_with_lowercase
            && symbol
                .get(..starts_with.len())
                .map(|s| s.eq_ignore_ascii_case(starts_with))
                != Some(true)
        {
            return false;
        }
        self.added_names.insert(symbol)
    }

    fn maybe_add_tree_name(
        &mut self,
        file: &'db PythonFile,
        scope: Scope,
        name_def: NameDef<'db>,
        in_class: bool,
    ) {
        let name = name_def.as_code();
        if !self.maybe_add(name) {
            return;
        }
        let kind =
            find_kind_and_try_to_follow_imports(self.infos.db, file, scope, name_def, in_class);
        if let Some(result) = (self.on_result)(
            self.replace_range,
            &CompletionTreeName {
                db: self.infos.db,
                file,
                name: name_def.name(),
                kind,
            },
        ) {
            self.items
                .push((CompletionSortPriority::new_symbol(name), result))
        }
    }
}

fn find_kind_and_try_to_follow_imports(
    db: &Database,
    file: &PythonFile,
    scope: Scope,
    name_def: NameDef,
    in_class: bool,
) -> CompletionItemKind {
    if name_def.maybe_import().is_none() {
        return find_kind_for_name_def(db, file, scope, name_def, in_class);
    }
    let ref_ = NodeRef::new(file, name_def.index());
    let p = ref_.point();
    if p.calculated() {
        match p.kind() {
            PointKind::Redirect => {
                let node_ref = p.as_redirected_node_ref(db);
                if let Some(name) = node_ref.maybe_name()
                    && let Some(n) = name.name_def()
                {
                    return find_kind_and_try_to_follow_imports(
                        db,
                        node_ref.file,
                        Scope::Module,
                        n,
                        in_class,
                    );
                }
            }
            PointKind::FileReference => return CompletionItemKind::MODULE,
            PointKind::Complex => {
                if let Some(Type::Namespace(_)) = ref_.maybe_type() {
                    return CompletionItemKind::FOLDER;
                }
            }
            _ => (),
        }
    }
    match in_class {
        false => CompletionItemKind::VARIABLE,
        true => CompletionItemKind::FIELD,
    }
}

fn find_kind_for_name_def(
    db: &Database,
    file: &PythonFile,
    scope: Scope,
    name_def: NameDef,
    in_class: bool,
) -> CompletionItemKind {
    let mut kind = match in_class {
        false => CompletionItemKind::VARIABLE,
        true => CompletionItemKind::FIELD,
    };
    if let Some(func) = name_def.maybe_name_of_func() {
        kind = if in_class {
            if matches!(name_def.as_code(), "__init__" | "__new__") {
                CompletionItemKind::CONSTRUCTOR
            } else {
                let f = Function::new_with_unknown_parent(db, NodeRef::new(file, func.index()));
                with_i_s_non_self(db, file, scope, |i_s| {
                    f.ensure_cached_func(i_s);
                    match f.kind(i_s) {
                        FunctionKind::Function { .. } => CompletionItemKind::METHOD,
                        FunctionKind::Property { .. } => CompletionItemKind::PROPERTY,
                        FunctionKind::Classmethod { .. } | FunctionKind::Staticmethod => {
                            CompletionItemKind::FUNCTION
                        }
                    }
                })
            }
        } else {
            CompletionItemKind::FUNCTION
        }
    } else if let Some(class) = name_def.maybe_name_of_class() {
        kind = CompletionItemKind::CLASS;
        if let Some(class_infos) =
            ClassNodeRef::new(file, class.index()).maybe_cached_class_infos(db)
            && matches!(class_infos.kind, ClassKind::Enum)
        {
            kind = CompletionItemKind::ENUM
        }
    }
    kind
}

pub(crate) struct ScopesIterator<'db> {
    pub file: &'db PythonFile,
    pub only_reachable: bool,
    pub current: Option<Scope<'db>>,
}

impl<'db> Iterator for ScopesIterator<'db> {
    type Item = Scope<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.take()?;
        let mut parent_scope = |scope| match scope {
            Scope::Module => Ok(()),
            Scope::Class(c) => Err(ClassNodeRef::new(self.file, c.index())
                .class_storage()
                .parent_scope),
            Scope::Function(f) => Err(FuncNodeRef::new(self.file, f.index()).parent_scope()),
            Scope::Lambda(l) => {
                self.current = Some(l.parent_scope());
                Ok(())
            }
        };
        let mut check = result;
        loop {
            match parent_scope(check) {
                // Case was already handled
                Ok(()) => (),
                Err(ParentScope::Module) => {
                    self.current = Some(Scope::Module);
                }
                Err(ParentScope::Function(f)) => {
                    self.current = Some(Scope::Function(FunctionDef::by_index(&self.file.tree, f)));
                }
                Err(ParentScope::Class(c)) => {
                    check = Scope::Class(ClassDef::by_index(&self.file.tree, c));
                    if self.only_reachable {
                        // Parent classes are not reachable for name lookups and therefore need to be
                        // skipped
                        continue;
                    } else {
                        self.current = Some(check);
                    }
                }
            }
            return Some(result);
        }
    }
}

pub trait Completion {
    fn label(&self) -> &str;
    fn insert_text(&self) -> String {
        self.label().to_string()
    }
    fn kind(&self) -> CompletionItemKind;
    fn file_path(&self) -> Option<&str>;
    fn deprecated(&self) -> bool {
        false
    }
    fn documentation(&self) -> Option<Cow<'_, str>> {
        None
    }
}

struct CompletionTreeName<'db> {
    db: &'db Database,
    file: &'db PythonFile,
    name: Name<'db>,
    kind: CompletionItemKind,
}

impl<'db> Completion for CompletionTreeName<'db> {
    fn label(&self) -> &str {
        self.name.as_code()
    }

    fn kind(&self) -> CompletionItemKind {
        self.kind
    }

    fn file_path(&self) -> Option<&str> {
        Some(self.file.file_path(self.db))
    }

    fn documentation(&self) -> Option<Cow<'db, str>> {
        let doc = self.name.clean_docstring();
        if doc.is_empty()
            && let Some(r) = try_to_follow_imports(self.db, self.file, self.name)
        {
            return Some(match r {
                FollowImportResult::File(file_index) => {
                    let file = self.db.loaded_python_file(file_index);
                    ModuleName { db: self.db, file }.documentation()
                }
                FollowImportResult::TreeName(tree_name) => tree_name.documentation(),
            });
        }
        Some(process_docstring(self.file, doc, || {
            TreeName::with_unknown_parent_scope(self.db, self.file, self.name).goto_non_stub()
        }))
    }
}

struct CompletionDirEntry<'db, 'x> {
    db: &'db Database,
    name: &'db str,
    entry: &'x DirectoryEntry,
}

impl<'db> Completion for CompletionDirEntry<'db, '_> {
    fn label(&self) -> &str {
        self.name
    }

    fn kind(&self) -> CompletionItemKind {
        match self.entry {
            DirectoryEntry::File(_) => CompletionItemKind::MODULE,
            DirectoryEntry::Directory(_) => CompletionItemKind::FOLDER,
            _ => {
                recoverable_error!("Exptected no completion entry for {:?}", &self.entry);
                CompletionItemKind::MODULE
            }
        }
    }

    fn file_path(&self) -> Option<&str> {
        // TODO
        /*
        match &self.entry {
            DirectoryEntry::File(file_entry) => file_entry.absolute_path(),
            DirectoryEntry::Directory(_) => ...,
            DirectoryEntry::MissingEntry(missing_entry) => unreachable!(),
        }
        */
        None
    }

    fn documentation(&self) -> Option<Cow<'db, str>> {
        match self.entry {
            DirectoryEntry::File(entry) => Some(
                ModuleName {
                    db: self.db,
                    file: self.db.load_file_from_workspace(entry)?,
                }
                .documentation(),
            ),
            _ => None,
        }
    }
}

struct KeywordArgumentCompletion {
    keyword_argument: String,
}

impl Completion for KeywordArgumentCompletion {
    fn label(&self) -> &str {
        &self.keyword_argument
    }

    fn kind(&self) -> CompletionItemKind {
        CompletionItemKind::UNIT // Not sure what to choose, but I think this is fine.
    }

    fn file_path(&self) -> Option<&str> {
        None
    }
}

struct KeywordCompletion {
    keyword: &'static str,
}

impl Completion for KeywordCompletion {
    fn label(&self) -> &str {
        self.keyword
    }

    fn kind(&self) -> CompletionItemKind {
        CompletionItemKind::KEYWORD
    }

    fn file_path(&self) -> Option<&str> {
        None
    }
}

struct EnumMemberCompletion<'db> {
    db: &'db Database,
    enum_: &'db Enum,
    member: &'db EnumMemberDefinition,
}

impl Completion for EnumMemberCompletion<'_> {
    fn label(&self) -> &str {
        self.member.name(self.db)
    }

    fn kind(&self) -> CompletionItemKind {
        CompletionItemKind::ENUM_MEMBER
    }

    fn file_path(&self) -> Option<&str> {
        Some(self.db.file_path(self.enum_.defined_at.file))
    }
}

struct NamedTupleMemberCompletion<'db> {
    db: &'db Database,
    file: FileIndex,
    param: &'db CallableParam,
}

impl Completion for NamedTupleMemberCompletion<'_> {
    fn label(&self) -> &str {
        self.param.name.as_ref().unwrap().as_str(self.db)
    }

    fn kind(&self) -> CompletionItemKind {
        CompletionItemKind::FIELD
    }

    fn file_path(&self) -> Option<&str> {
        Some(self.db.file_path(self.file))
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
enum CompletionSortPriority<'db> {
    //Literal,    // e.g. TypedDict literal
    //NamedParam, // e.g. def foo(*, bar) => `foo(b` completes to bar=
    KeywordArgument,
    EnumMember,
    Default(&'db str),
    Dunder(&'db str), // e.g. __eq__
}

impl<'db> CompletionSortPriority<'db> {
    fn new_symbol(symbol: &'db str) -> Self {
        if symbol.starts_with("__") && symbol.ends_with("__") {
            Self::Dunder(symbol)
        } else {
            Self::Default(symbol)
        }
    }
}
