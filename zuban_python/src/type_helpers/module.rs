use crate::{
    arguments::KnownArgsWithCustomAddIssue,
    database::{Database, FileIndex, PointLink},
    debug,
    diagnostics::IssueKind,
    file::{File, PythonFile},
    imports::{python_import, ImportResult},
    inference_state::InferenceState,
    inferred::Inferred,
    matching::LookupResult,
    node_ref::NodeRef,
    type_::{Namespace, Type},
    workspaces::Parent,
};

#[derive(Copy, Clone)]
pub struct Module<'a> {
    pub file: &'a PythonFile,
}

impl<'a> Module<'a> {
    pub fn new(file: &'a PythonFile) -> Self {
        Self { file }
    }

    pub fn from_file_index(db: &'a Database, file_index: FileIndex) -> Self {
        Self::new(db.loaded_python_file(file_index))
    }

    pub fn sub_module(&self, db: &'a Database, name: &str) -> Option<ImportResult> {
        let entry = self.file.file_entry(db);
        match &entry.parent {
            Parent::Directory(dir) => {
                if &*entry.name != "__init__.py" && &*entry.name != "__init__.pyi" {
                    return None;
                }
                python_import(db, self.file.file_index(), &dir.upgrade().unwrap(), name)
            }
            Parent::Workspace(_) => None,
        }
    }

    pub(crate) fn lookup(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
    ) -> LookupResult {
        self.lookup_with_is_import(i_s, add_issue, name, None)
    }

    pub(crate) fn lookup_with_is_import(
        &self,
        i_s: &InferenceState,
        add_issue: impl Fn(IssueKind),
        name: &str,
        // Coming from an import we need to make sure that we do not create loops for imports
        original_import_name_to_be_defined: Option<PointLink>,
    ) -> LookupResult {
        if let Some(link) = self
            .file
            .lookup_global(name)
            .filter(|link| original_import_name_to_be_defined != Some((*link).into()))
        {
            let link = link.into();
            if is_reexport_issue_if_check_needed(i_s.db, self.file, link) {
                add_issue(IssueKind::ImportStubNoExplicitReexport {
                    module_name: self.file.qualified_name(i_s.db).into(),
                    attribute: name.into(),
                })
            }
            LookupResult::GotoName {
                name: link,
                inf: if original_import_name_to_be_defined.is_some() {
                    Inferred::from_saved_link(link)
                } else {
                    self.file
                        .inference(i_s)
                        .infer_name_of_definition_by_index(link.node_index)
                },
            }
        } else if let Some(sub_module) = self.sub_module(i_s.db, name) {
            match sub_module {
                ImportResult::File(file_index) => LookupResult::FileReference(file_index),
                ImportResult::Namespace { .. } => todo!(),
            }
        } else if let Some(link) = self
            .file
            .inference(i_s)
            .lookup_from_star_import(name, false)
        {
            let inf = if original_import_name_to_be_defined.is_some() {
                Inferred::from_saved_link(link)
            } else {
                i_s.db
                    .loaded_python_file(link.file)
                    .inference(i_s)
                    .infer_name_of_definition_by_index(link.node_index)
            };
            LookupResult::GotoName { name: link, inf }
        } else if let Some(inf) = self.maybe_execute_getattr(i_s, &add_issue) {
            LookupResult::UnknownName(inf)
        } else if name == "__getattr__" {
            // There is a weird (and wrong) definition in typeshed that defines __getattr__ on
            // ModuleType:
            // https://github.com/python/typeshed/blob/516f6655051b061652f086445ea54e8e82232349/stdlib/types.pyi#L352
            LookupResult::None
        } else {
            i_s.db
                .python_state
                .module_instance()
                .type_lookup(i_s, add_issue, name)
        }
    }

    pub(crate) fn maybe_execute_getattr(
        &self,
        i_s: &InferenceState,
        add_issue: &'a dyn Fn(IssueKind),
    ) -> Option<Inferred> {
        self.file.lookup_global("__getattr__").map(|link| {
            let inf = i_s
                .db
                .loaded_python_file(link.file)
                .inference(i_s)
                .infer_name_of_definition_by_index(link.node_index);
            inf.execute(
                i_s,
                &KnownArgsWithCustomAddIssue::new(
                    &Inferred::from_type(i_s.db.python_state.str_type()),
                    add_issue,
                ),
            )
        })
    }
}

pub fn lookup_in_namespace(
    db: &Database,
    from_file: FileIndex,
    namespace: &Namespace,
    name: &str,
) -> LookupResult {
    match python_import(db, from_file, &namespace.content, name) {
        Some(ImportResult::File(file_index)) => LookupResult::FileReference(file_index),
        Some(ImportResult::Namespace(namespace)) => {
            LookupResult::UnknownName(Inferred::from_type(Type::Namespace(namespace)))
        }
        None => {
            debug!("TODO namespace basic lookups");
            LookupResult::None
        }
    }
}

pub fn is_reexport_issue_if_check_needed(
    db: &Database,
    file: &PythonFile,
    link: PointLink,
) -> bool {
    if let Some(dunder_all) = file.maybe_dunder_all(db) {
        let name = NodeRef::from_link(db, link).maybe_name().unwrap().as_code();
        !(dunder_all.iter().any(|d| d.as_str(db) == name) || name == "__all__")
    } else {
        let check_reexport = file.is_stub || file.flags(db).no_implicit_reexport;
        check_reexport && is_private_import(db, link)
    }
}

pub fn is_private_import(db: &Database, link: PointLink) -> bool {
    NodeRef::from_link(db, link)
        .maybe_name()
        .unwrap()
        .name_definition()
        .unwrap()
        .maybe_import()
        .is_some_and(|i| !i.is_stub_reexport())
}
