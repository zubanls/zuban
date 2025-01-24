#![allow(unreachable_code, unused_imports)]
use std::{fs, path::PathBuf};

fn main() -> std::io::Result<()> {
    /*
    let mut project = zuban_python::Project::new("foo".to_owned());
    let script = zuban_python::Script::new(
        &mut project,
        Some("/foo/bar.py".to_owned()),
        Some("foo\n".to_owned()),
    );
    let defs = script.infer_definition(
        &|name| (name.kind(), name.name().to_owned()),
        zuban_python::Position::Byte(1),
    );
    for (kind, name) in defs {
        dbg!(kind, name);
    }
    */

    Ok(())

    /*
    let file = "/home/dave/source/stuff_jedi/quickfix_huge.py";
    let contents = fs::read_to_string(file)?;

    let c = contents.repeat(10);
    let start = std::time::Instant::now();
    parsa_python::parse(c);
    eprintln!("elapsed {:?}", start.elapsed());

    for _ in 0..10 {
        let c = contents.repeat(10);
        let start = std::time::Instant::now();
        parsa_python::parse(c);
        eprintln!("elapsed {:?}", start.elapsed());
    }
    Ok(())
    */
}
