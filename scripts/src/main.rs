use std::fs;
use std::path::PathBuf;

fn main() -> std::io::Result<()> {
    let mut project = zuban_python::Project::new("foo".to_owned());
    zuban_python::Script::new(&mut project, Some(PathBuf::from("/foo/bar")), None);

    return Ok(());

    let file = "/home/dave/source/stuff_jedi/quickfix_huge.py";
    let contents = fs::read_to_string(file)?;

    let c = contents.repeat(10);
    let start = std::time::Instant::now();
    parsa_python::PYTHON_GRAMMAR.parse(c);
    eprintln!("elapsed {:?}", start.elapsed());

    for _ in 0..10 {
        let c = contents.repeat(10);
        let start = std::time::Instant::now();
        parsa_python::PYTHON_GRAMMAR.parse(c);
        eprintln!("elapsed {:?}", start.elapsed());
    }
    Ok(())
}
