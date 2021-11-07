mod cases;

use std::env;
use std::fs::{read_dir, read_to_string};
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let cli_args: Vec<String> = env::args().collect();
    let mut filters = vec![];
    let mut negative_filters = vec![];
    if cli_args.len() > 1 {
        for c in &cli_args[1..] {
            if c.starts_with("!") {
                negative_filters.push(&c[1..]);
            } else if c != "blackbox" {
                filters.push(c);
            }
        }
    }

    let files = python_files();
    let start = Instant::now();
    let mut count = 0;
    let file_count = files.len();
    for python_file in files {
        let file_name = python_file.file_name().unwrap().to_str().unwrap();
        if (filters.len() == 0 || filters.iter().any(|x| file_name.contains(*x)))
            && !negative_filters.iter().any(|x| file_name.contains(*x))
        {
            let code = read_to_string(&python_file).unwrap();
            let f = cases::TestFile {
                path: python_file,
                code,
            };
            count += f.test();
        }
    }
    println!(
        "Run {} integration tests in {} files; finished in {:.2}s",
        count,
        file_count,
        start.elapsed().as_secs_f32(),
    );
}

fn python_files() -> Vec<PathBuf> {
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
