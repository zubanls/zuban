use std::{
    fs,
    ops::Deref,
    path::{Path, PathBuf},
    str::FromStr,
};

use lsp_types::{TextDocumentIdentifier, Uri};
use serde::Serialize;
use serde_json::{to_string_pretty, Value};
use test_utils::{calculate_steps, dedent};

use crate::{connection::Connection, testdir::TestDir};

pub(crate) struct Project<'a> {
    fixture: &'a str,
    roots: Vec<String>,
    root_dir_contains_symlink: bool,
}

impl<'a> Project<'a> {
    pub(crate) fn with_fixture(fixture: &'a str) -> Self {
        logging_config::setup_logging_for_tests();
        Self {
            fixture,
            roots: vec![],
            root_dir_contains_symlink: false,
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

    pub(crate) fn into_server(self) -> Server {
        let tmp_dir = if self.root_dir_contains_symlink {
            TestDir::new_symlink()
        } else {
            TestDir::new()
        };
        let dedented_fixture = dedent(&self.fixture);
        for entry in fixture_to_file_entry(&dedented_fixture) {
            let path = Path::new(tmp_dir.path()).join(&entry.path['/'.len_utf8()..]);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path.as_path(), entry.text.as_bytes()).unwrap();
        }
        // TODO let tmp_dir_path = AbsPathBuf::assert(tmp_dir.path().to_path_buf());
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
            ),
        }
    }
}

pub(crate) struct Server {
    tmp_dir: TestDir,
    connection: Connection,
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
            uri: Uri::from_str(&path_to_uri(&path)).unwrap(),
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
}

struct FileEntry<'x> {
    path: &'x str,
    text: &'x str,
}

fn fixture_to_file_entry(fixture: &str) -> impl Iterator<Item = FileEntry> {
    let steps = calculate_steps(None, fixture);
    assert!(
        steps.flags.is_empty(),
        "For now flags in fixtures are not supported"
    );
    assert_eq!(steps.steps.len(), 1, "For now we only support one step");
    let first = steps.steps.into_iter().next().unwrap();
    assert!(first.out.is_empty());
    assert!(first.deletions.is_empty());
    first
        .files
        .into_iter()
        .map(|(path, text)| FileEntry { path, text })
}

fn join(path: &str, other: &str) -> String {
    Path::new(path)
        .join(other)
        .into_os_string()
        .into_string()
        .unwrap()
}

fn path_to_uri(path: &str) -> String {
    format!("file:///{path}")
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
