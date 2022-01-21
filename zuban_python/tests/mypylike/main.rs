use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;
use std::time::Instant;

use regex::Regex;

#[derive(Debug)]
struct TestCase {
    file_name: OsString,
    name: String,
}

fn main() {
    let mut project = zuban_python::Project::new("foo".to_owned());

    let files = find_mypy_style_files();
    let start = Instant::now();
    let mut full_count = 0;
    let mut ran_count = 0;
    let file_count = files.len();
    for file in files {
        for case in mypy_style_cases(file.file_stem().unwrap(), read_to_string(&file).unwrap()) {
            dbg!(case);
        }
        /*
        let f = cases::TestFile {
            path: file,
            code,
            filters: &filters,
        };
        let (ran, full) = f.test(&mut project);
        ran_count += ran;
        full_count += full;
        */
    }
    println!(
        "Ran {} of {} mypy-like tests in {} files; finished in {:.2}s",
        ran_count,
        full_count,
        file_count,
        start.elapsed().as_secs_f32(),
    );
}

fn mypy_style_cases(file_name: &OsStr, code: String) -> Vec<TestCase> {
    let case_regex = Regex::new(r"\n\[case ([a-zA-Z_0-9-]+)\][ \t]*\n").unwrap();
    let mut cases = vec![];

    let mut start = None;
    for capture in case_regex.captures_iter(&code) {
        if let Some(end) = start {
            // capture.get(0).unwrap().start() - 1, end
            cases.push(TestCase {
                file_name: file_name.to_owned(),
                name: capture.get(1).unwrap().as_str().to_owned(),
            });
        }
        start = Some(capture.get(0).unwrap().end())
    }
    cases
}

fn find_mypy_style_files() -> Vec<PathBuf> {
    let mut base = PathBuf::from(file!().replace("zuban_python/", ""));
    assert!(base.pop());

    let mut entries = vec![];
    for p in ["from_mypy", "tests"] {
        let mut path = base.clone();
        path.push(p);

        entries.extend(
            read_dir(path)
                .unwrap()
                .map(|res| res.map(|e| e.path()).unwrap()),
        );
    }
    entries.sort();
    entries
}
