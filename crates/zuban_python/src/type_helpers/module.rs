use crate::{
    database::Database,
    debug,
    file::PythonFile,
    imports::{namespace_import, ImportResult},
    inferred::Inferred,
    node_ref::NodeRef,
    type_::{AnyCause, LookupResult, Namespace, Type},
};

pub fn lookup_in_namespace(
    db: &Database,
    from_file: &PythonFile,
    namespace: &Namespace,
    name: &str,
) -> LookupResult {
    match namespace_import(db, from_file, namespace, name) {
        Some(ImportResult::File(file_index)) => LookupResult::FileReference(file_index),
        Some(ImportResult::Namespace(namespace)) => {
            LookupResult::UnknownName(Inferred::from_type(Type::Namespace(namespace)))
        }
        Some(ImportResult::PyTypedMissing) => LookupResult::any(AnyCause::FromError),
        None => {
            debug!("TODO namespace basic lookups");
            LookupResult::None
        }
    }
}

pub fn is_reexport_issue(db: &Database, name_ref: NodeRef) -> bool {
    if !name_ref.file.is_stub() && !name_ref.file.flags(db).no_implicit_reexport {
        return false;
    }
    if let Some(dunder_all) = name_ref.file.maybe_dunder_all(db) {
        debug_assert!(name_ref.maybe_name().is_some());
        let name = name_ref.as_code();
        if dunder_all.iter().any(|d| d.as_str(db) == name) || name == "__all__" {
            // Name was exported in __all__
            return false;
        }
    }
    is_private_import(name_ref)
}

pub fn is_private_import(name_ref: NodeRef) -> bool {
    name_ref
        .maybe_import_of_name_in_symbol_table()
        .is_some_and(|i| !i.is_stub_reexport())
}
