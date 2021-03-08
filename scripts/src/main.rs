use std::fs;
use parsa_python;

fn main() -> std::io::Result<()> {
    let file = "/home/dave/source/stuff_jedi/quickfix_huge.py";
    let contents = fs::read_to_string(file)?;

    let contents = contents.repeat(10);
    let start = std::time::Instant::now();
    parsa_python::PYTHON_GRAMMAR.parse(&contents);
    eprintln!("elapsed {:?}", start.elapsed()); // note :?

    for _ in 0..10 {
        let start = std::time::Instant::now();
        parsa_python::PYTHON_GRAMMAR.parse(&contents);
        eprintln!("elapsed {:?}", start.elapsed()); // note :?
    }
    Ok(())
}
