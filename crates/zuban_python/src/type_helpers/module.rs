use crate::{
    database::Database,
    debug,
    file::PythonFile,
    imports::{namespace_import, ImportResult},
    inferred::Inferred,
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
