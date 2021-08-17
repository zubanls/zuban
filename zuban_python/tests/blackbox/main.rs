mod cases;

use std::env;
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;

fn main() {
    let cli_args: Vec<String> = env::args().collect();
    if cli_args.len() > 1 {
        // TODO filtering
    }

    for python_file in get_python_files() {
        let code = read_to_string(&python_file).unwrap();
        cases::TestFile {path: python_file, code}.test();
    }
}

fn get_python_files() -> Vec<PathBuf> {
    let mut p = PathBuf::from(file!().replace("zuban_python/", ""));
    assert!(p.pop());
    p.push("python_files");

    let mut entries: Vec<_> = read_dir(p)
        .unwrap()
        .map(|res| res.map(|e| e.path()).unwrap())
        .collect();
    entries.sort();
    entries
}
