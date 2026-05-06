use parsa_python_cst::{
    ArgumentsDetails, GotoNode, NameParent, NodeIndex, Primary, PrimaryContent, Scope,
};
use regex::{Matches, Regex};

use crate::{
    arguments::SimpleArgs,
    database::{Database, PointKind, PointLink},
    file::PythonFile,
    goto::{FollowImportResult, check_node_ref_and_maybe_follow_import},
    inference_state::InferenceState,
};

// Stats from a 2016 Lenovo Notebook running Linux:
// With os.walk, it takes about 10s to scan 11'000 files (without filesystem
// caching). Once cached it only takes 5s.
const OPENED_FILE_LIMIT: usize = 200;
const PARSED_FILE_LIMIT: usize = 10;
const MAX_PARAM_SEARCHES: usize = 20;
const PER_FILE_SEARCH_NAME_LIMIT: usize = 20;

fn search_callable_arguments(
    i_s: &InferenceState,
    wanted: PointLink,
    search_in_file: &PythonFile,
    name: &str,
) {
    let regex = Regex::new(&format!(r"\b{name}\b(")).unwrap();
    for execution in FileNameSearcher::new(i_s.db, search_in_file, &regex, wanted) {
        /*
        // The deeper we're in the recursion, the less code should be inferred.
        if i * inference_state.dynamic_params_depth > MAX_PARAM_SEARCHES {
            found_arguments = True;
            yield arguments
        }
        */
    }
}

struct PotentialFileIterator<'db> {
    file: &'db PythonFile,
    //already_checked: HashSet<Arc<FileEntry>>,
}

impl<'db> Iterator for PotentialFileIterator<'db> {
    type Item = &'db PythonFile;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

struct FileNameSearcher<'db, 'regex> {
    db: &'db Database,
    potential_files: PotentialFileIterator<'db>,
    regex: &'regex Regex,
    current_file: &'db PythonFile,
    wanted: PointLink,
    matches: std::iter::Take<Matches<'regex, 'db>>,
    found_in_current_file: bool,
}

impl<'db, 'regex> FileNameSearcher<'db, 'regex> {
    fn new(
        db: &'db Database,
        file: &'db PythonFile,
        regex: &'regex Regex,
        wanted: PointLink,
    ) -> Self {
        Self {
            db,
            potential_files: PotentialFileIterator { file },
            regex,
            current_file: file,
            wanted,
            matches: regex
                .find_iter(file.tree.code())
                .take(PER_FILE_SEARCH_NAME_LIMIT),
            found_in_current_file: false,
        }
    }
}

struct FoundExecution<'db> {
    file: &'db PythonFile,
    scope: Scope<'db>,
    primary: Primary<'db>,
    details: ArgumentsDetails<'db>,
}

impl<'db> Iterator for FileNameSearcher<'db, '_> {
    type Item = FoundExecution<'db>;

    fn next(&mut self) -> Option<Self::Item> {
        for match_ in &mut self.matches {
            let (scope, node) = self
                .current_file
                .tree
                .goto_node(match_.range().start as NodeIndex);
            if let GotoNode::Name(name) = node
                && let NameParent::Primary(primary) = name.parent()
                && let PrimaryContent::Execution(details) = primary.second()
            {
                if matches!(details, ArgumentsDetails::None) {
                    continue;
                }
                let result = self.current_file.ensure_calculated_diagnostics(self.db);
                debug_assert!(result.is_ok());
                let point = self.current_file.points.get(name.index());
                if point.calculated() && point.kind() == PointKind::Redirect {
                    let node_ref = point.as_redirected_node_ref(self.db);
                    if let Some(FollowImportResult::TreeName(tree_name)) =
                        check_node_ref_and_maybe_follow_import(self.db, node_ref, true)
                        && tree_name.file.file_index == self.wanted.file
                        && tree_name.cst_name.index() == self.wanted.node_index
                    {
                        self.found_in_current_file = true;
                        return Some(FoundExecution {
                            file: self.current_file,
                            scope,
                            primary,
                            details,
                        });
                    }
                }
            }
        }
        if self.found_in_current_file {
            // If there are results after processing a module where we have found a result,
            // we're probably good to abort. This is a speed optimization.
            return None;
        }
        self.current_file = self.potential_files.next()?;
        self.matches = self
            .regex
            .find_iter(self.current_file.tree.code())
            .take(PER_FILE_SEARCH_NAME_LIMIT);
        self.next()
    }
}
