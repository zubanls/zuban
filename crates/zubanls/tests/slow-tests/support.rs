use std::{
    cell::Cell,
    collections::HashMap,
    ops::Deref,
    path::{Path, PathBuf},
    str::FromStr,
    sync::{atomic::Ordering, Mutex},
};

use lsp_types::{
    notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument},
    request::DocumentDiagnosticRequest,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DocumentDiagnosticParams, DocumentDiagnosticReport, DocumentDiagnosticReportResult,
    PartialResultParams, TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem,
    Uri, VersionedTextDocumentIdentifier, WorkDoneProgressParams,
};
use serde::Serialize;
use serde_json::{to_string_pretty, Value};
use test_utils::{write_files_from_fixture, TestDir};
use zubanls::GLOBAL_NOTIFY_EVENT_COUNTER;

use crate::connection::{path_to_uri, Connection};

lazy_static::lazy_static! {
    static ref FILE_SYSTEM_LOCK: Mutex<()> = Mutex::default();
}

pub(crate) struct Project<'a> {
    fixture: &'a str,
    roots: Vec<String>,
    root_dir_contains_symlink: bool,
    push_diagnostics: bool,
}

impl<'a> Project<'a> {
    pub(crate) fn with_fixture(fixture: &'a str) -> Self {
        logging_config::setup_logging_for_tests();
        Self {
            fixture,
            roots: vec![],
            root_dir_contains_symlink: false,
            push_diagnostics: false,
        }
    }

    pub(crate) fn root(mut self, path: &str) -> Self {
        self.roots.push(path.into());
        self
    }

    pub(crate) fn with_root_dir_contains_symlink(mut self) -> Self {
        self.root_dir_contains_symlink = true;
        self
    }

    pub(crate) fn with_push_diagnostics(mut self) -> Self {
        self.push_diagnostics = true;
        self
    }

    pub(crate) fn into_server(self) -> Server {
        self.into_server_detailed(None)
    }

    pub(crate) fn into_server_detailed(
        self,
        client_encodings: Option<Vec<lsp_types::PositionEncodingKind>>,
    ) -> Server {
        // TODO let tmp_dir_path = AbsPathBuf::assert(tmp_dir.path().to_path_buf());
        let tmp_dir = write_files_from_fixture(self.fixture, self.root_dir_contains_symlink);
        let tmp_dir_path = tmp_dir.path();
        let mut roots = self
            .roots
            .into_iter()
            .map(|root| {
                PathBuf::from_str(tmp_dir_path)
                    .unwrap()
                    .join(root)
                    .into_os_string()
                    .into_string()
                    .unwrap()
            })
            .collect::<Vec<String>>();
        if roots.is_empty() {
            roots.push(tmp_dir_path.into());
        }
        Server {
            tmp_dir,
            connection: Connection::initialized(
                &roots.iter().map(|root| root.as_str()).collect::<Vec<_>>(),
                client_encodings,
                !self.push_diagnostics,
            ),
            version_incrementor: Default::default(),
        }
    }
}

pub(crate) struct Server {
    pub tmp_dir: TestDir,
    connection: Connection,
    version_incrementor: Cell<i32>,
}

impl Deref for Server {
    type Target = Connection;

    fn deref(&self) -> &Self::Target {
        &self.connection
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.connection.shutdown_and_exit()
    }
}

impl Server {
    pub(crate) fn doc_id(&self, rel_path: &str) -> TextDocumentIdentifier {
        let path = join(self.tmp_dir.path(), rel_path);
        TextDocumentIdentifier {
            uri: path_to_uri(&path),
        }
    }

    pub(crate) fn request_and_expect_json<R>(&self, params: R::Params, expected_resp: Value)
    where
        R: lsp_types::request::Request,
        R::Params: Serialize,
    {
        let response = self.connection.request_with_response::<R>(params);
        if let Some(err) = response.error {
            panic!("error response: {err:#?}");
        }
        let actual = response.result.unwrap();

        if let Some((expected_part, actual_part)) = find_mismatch(&expected_resp, &actual) {
            panic!(
                "JSON mismatch\nExpected:\n{}\nWas:\n{}\nExpected part:\n{}\nActual part:\n{}\n",
                to_string_pretty(&expected_resp).unwrap(),
                to_string_pretty(&actual).unwrap(),
                to_string_pretty(expected_part).unwrap(),
                to_string_pretty(actual_part).unwrap(),
            );
        }
    }

    pub(crate) fn diagnostics_for_file(&self, rel_path: &str) -> Vec<String> {
        let items = self.full_diagnostics_for_file(rel_path);
        items.into_iter().map(|d| d.message).collect()
    }

    pub(crate) fn full_diagnostics_for_file(&self, rel_path: &str) -> Vec<lsp_types::Diagnostic> {
        self.full_diagnostics_for_abs_path(self.doc_id(rel_path))
    }

    pub(crate) fn full_diagnostics_for_abs_path(
        &self,
        text_document: TextDocumentIdentifier,
    ) -> Vec<lsp_types::Diagnostic> {
        let res = self.request::<DocumentDiagnosticRequest>(DocumentDiagnosticParams {
            text_document,
            identifier: None,
            previous_result_id: None,
            partial_result_params: PartialResultParams::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
        });
        let DocumentDiagnosticReportResult::Report(DocumentDiagnosticReport::Full(report)) = res
        else {
            unreachable!()
        };
        assert!(report.related_documents.is_none());
        report.full_document_diagnostic_report.items
    }

    pub fn expect_multiple_diagnostics_pushes_with_uris<'x>(
        &self,
        pushes: impl Into<HashMap<&'x str, Vec<&'x str>>>,
    ) {
        let mut pushes = pushes.into();
        while !pushes.is_empty() {
            let (uri, diags) = self.expect_publish_diagnostics_with_uri();
            let uri = uri.as_str();
            if let Some(wanted) = pushes.remove(uri) {
                assert_eq!(diags, wanted);
            } else {
                let keys = pushes.keys().collect::<Vec<_>>();
                panic!("Expected diagnostic for one of {keys:?}, but found {uri} ({diags:?})")
            }
        }
    }

    pub fn expect_multiple_diagnostics_pushes<'x>(
        &self,
        pushes: impl Into<HashMap<&'x str, Vec<&'x str>>>,
    ) {
        let mut pushes = pushes.into();
        while !pushes.is_empty() {
            let (uri, diags) = self.expect_publish_diagnostics();
            let uri = uri.as_str();
            if let Some(wanted) = pushes.remove(uri) {
                assert_eq!(diags, wanted);
            } else {
                let keys = pushes.keys().collect::<Vec<_>>();
                panic!("Expected diagnostic for one of {keys:?}, but found {uri} ({diags:?})")
            }
        }
    }

    pub fn expect_publish_diagnostics_for_file(&self, for_file: &str) -> Vec<String> {
        let (file, diags) = self.expect_publish_diagnostics();
        assert_eq!(for_file, file);
        diags
    }

    pub fn expect_publish_diagnostics(&self) -> (String, Vec<String>) {
        let (uri, messages) = self.expect_publish_diagnostics_with_uri();
        (
            uri.as_str()
                .strip_prefix("file://")
                .unwrap()
                .strip_prefix(&self.tmp_dir.path_for_uri())
                .unwrap()
                .strip_prefix('/')
                .unwrap()
                .to_string(),
            messages,
        )
    }

    pub fn expect_publish_diagnostics_with_uri(&self) -> (Uri, Vec<String>) {
        let publish = self.expect_notification::<lsp_types::notification::PublishDiagnostics>();
        (
            publish.uri,
            publish.diagnostics.into_iter().map(|d| d.message).collect(),
        )
    }

    fn with_wait(&self, callback: impl FnOnce()) {
        // We need the lock to be able to use the global notify counter and be sure that no other
        // thread modifies it.
        let lock = FILE_SYSTEM_LOCK.lock();
        let current = GLOBAL_NOTIFY_EVENT_COUNTER.load(Ordering::SeqCst);
        callback();
        // Make sure the removal event appears before the LSP event.
        // Wait for a while (at least 5s)
        for _ in 0..5000 {
            std::thread::sleep(std::time::Duration::from_millis(1));
            if current < GLOBAL_NOTIFY_EVENT_COUNTER.load(Ordering::SeqCst) {
                drop(lock);
                // Just try and make tests fail less.
                std::thread::sleep(std::time::Duration::from_millis(
                    // For whatever reason Mac with FSEvents needs more sleep
                    if cfg!(target_os = "macos") { 10 } else { 1 },
                ));
                return;
            }
        }
        unreachable!("Reached a timeout");
    }

    pub(crate) fn raise_and_recover_panic_in_language_server(&self) {
        self.connection
            .send(lsp_server::Notification::new("test-panic".to_string(), ()));

        let message = self.connection.expect_notification_message();
        assert_eq!(message.typ, lsp_types::MessageType::ERROR);
        let message = message.message;

        // Check the hook
        assert!(
            message
                .starts_with("ZubanLS paniced, please open an issue on GitHub with the details:"),
            "{message}"
        );
        // Check the message
        assert!(message.contains("Test Panic"), "{message}");
        // Check for traceback occurrence
        assert!(
            message.contains("zubanls::server::GlobalState::event_loop"),
            "{message}"
        );
        assert!(
            message.contains("zubanls::notification_handlers::"),
            "{message}"
        );
    }

    pub fn change_in_memory_file(&self, path: &str, code: &str) {
        self.version_incrementor
            .set(self.version_incrementor.get() + 1);
        self.notify::<DidChangeTextDocument>(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: self.doc_id(path).uri,
                version: self.version_incrementor.get(),
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                text: code.to_string(),
                range: None,
                range_length: None,
            }],
        });
    }

    pub fn open_in_memory_file(&self, path: &str, code: &str) {
        self.open_in_memory_file_for_uri(self.doc_id(path).uri, code)
    }

    pub fn open_in_memory_file_for_uri(&self, uri: lsp_types::Uri, code: &str) {
        self.notify::<DidOpenTextDocument>(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri,
                language_id: "python".to_owned(),
                version: 0,
                text: code.to_owned(),
            },
        })
    }

    pub fn close_in_memory_file(&self, path: &str) {
        self.notify::<DidCloseTextDocument>(DidCloseTextDocumentParams {
            text_document: self.doc_id(path),
        });
    }

    pub(crate) fn write_file_and_wait(&self, rel_path: &str, code: &str) {
        let _p = tracing::info_span!("write_file_and_wait").entered();
        tracing::info!("Start");
        self.with_wait(|| self.tmp_dir.write_file(rel_path, code));
        tracing::info!("End");
    }

    pub(crate) fn remove_file_and_wait(&self, rel_path: &str) {
        let _p = tracing::info_span!("remove_file_and_wait").entered();
        tracing::info!("Start");
        self.with_wait(|| self.tmp_dir.remove_file(rel_path));
        tracing::info!("End");
    }

    pub(crate) fn rename_file_and_wait(&self, from: &str, to: &str) {
        let _p = tracing::info_span!("rename_file_and_wait").entered();
        tracing::info!("Start");
        self.with_wait(|| self.tmp_dir.rename(from, to));
        tracing::info!("End");
    }

    pub(crate) fn create_dir_all_and_wait(&self, rel_path: &str) {
        let _p = tracing::info_span!("create_dir_all_and_wait").entered();
        tracing::info!("Start");
        self.with_wait(|| self.tmp_dir.create_dir_all(rel_path));
        tracing::info!("End");
    }

    pub(crate) fn create_symlink_dir_and_wait(&self, rel_original: &str, rel_link: &str) {
        let _p = tracing::info_span!("create_symlink_dir_and_wait").entered();
        tracing::info!("Initiate create");
        self.with_wait(|| self.tmp_dir.create_symlink_dir(rel_original, rel_link));
        tracing::info!("End");
    }
}

fn join(path: &str, other: &str) -> String {
    Path::new(path)
        .join(other)
        .into_os_string()
        .into_string()
        .unwrap()
}

// Comparison functionality borrowed from cargo:

/// Compares JSON object for approximate equality.
/// You can use `[..]` wildcard in strings (useful for OS dependent things such
/// as paths). You can use a `"{...}"` string literal as a wildcard for
/// arbitrary nested JSON. Arrays are sorted before comparison.
fn find_mismatch<'a>(expected: &'a Value, actual: &'a Value) -> Option<(&'a Value, &'a Value)> {
    match (expected, actual) {
        (Value::Number(l), Value::Number(r)) if l == r => None,
        (Value::Bool(l), Value::Bool(r)) if l == r => None,
        (Value::String(l), Value::String(r)) if lines_match(l, r) => None,
        (Value::Array(l), Value::Array(r)) => {
            if l.len() != r.len() {
                return Some((expected, actual));
            }

            let mut l = l.iter().collect::<Vec<_>>();
            let mut r = r.iter().collect::<Vec<_>>();

            l.retain(
                |l| match r.iter().position(|r| find_mismatch(l, r).is_none()) {
                    Some(i) => {
                        r.remove(i);
                        false
                    }
                    None => true,
                },
            );

            if !l.is_empty() {
                assert!(!r.is_empty());
                Some((l[0], r[0]))
            } else {
                assert_eq!(r.len(), 0);
                None
            }
        }
        (Value::Object(l), Value::Object(r)) => {
            fn sorted_values(obj: &serde_json::Map<String, Value>) -> Vec<&Value> {
                let mut entries = obj.iter().collect::<Vec<_>>();
                entries.sort_by_key(|it| it.0);
                entries.into_iter().map(|(_k, v)| v).collect::<Vec<_>>()
            }

            let same_keys = l.len() == r.len() && l.keys().all(|k| r.contains_key(k));
            if !same_keys {
                return Some((expected, actual));
            }

            let l = sorted_values(l);
            let r = sorted_values(r);

            l.into_iter().zip(r).find_map(|(l, r)| find_mismatch(l, r))
        }
        (Value::Null, Value::Null) => None,
        // magic string literal "{...}" acts as wildcard for any sub-JSON
        (Value::String(l), _) if l == "{...}" => None,
        _ => Some((expected, actual)),
    }
}

/// Compare a line with an expected pattern.
/// - Use `[..]` as a wildcard to match 0 or more characters on the same line
///   (similar to `.*` in a regex).
fn lines_match(expected: &str, actual: &str) -> bool {
    // Let's not deal with / vs \ (windows...)
    // First replace backslash-escaped backslashes with forward slashes
    // which can occur in, for example, JSON output
    let expected = expected.replace(r"\\", "/").replace('\\', "/");
    let mut actual: &str = &actual.replace(r"\\", "/").replace('\\', "/");
    for (i, part) in expected.split("[..]").enumerate() {
        match actual.find(part) {
            Some(j) => {
                if i == 0 && j != 0 {
                    return false;
                }
                actual = &actual[j + part.len()..];
            }
            None => return false,
        }
    }
    actual.is_empty() || expected.ends_with("[..]")
}

#[test]
fn lines_match_works() {
    assert!(lines_match("a b", "a b"));
    assert!(lines_match("a[..]b", "a b"));
    assert!(lines_match("a[..]", "a b"));
    assert!(lines_match("[..]", "a b"));
    assert!(lines_match("[..]b", "a b"));

    assert!(!lines_match("[..]b", "c"));
    assert!(!lines_match("b", "c"));
    assert!(!lines_match("b", "cb"));
}
