use parsa_python_cst::Name;

use crate::{
    database::Database,
    debug,
    imports::{global_import, ImportResult},
};

use super::PythonFile;

impl PythonFile {
    pub(super) fn global_import(&self, db: &Database, name: Name) -> Option<ImportResult> {
        let result = global_import(db, self, name.as_str());
        if let Some(result) = &result {
            debug!(
                "Global import '{}': {:?}",
                name.as_code(),
                result.debug_info(db),
            );
        }
        result
    }
}
