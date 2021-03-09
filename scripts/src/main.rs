use std::fs;
use parsa_python;

fn main() -> std::io::Result<()> {
    let file = "/home/dave/source/stuff_jedi/quickfix_huge.py";
    let contents = fs::read_to_string(file)?;

    let c = contents.repeat(10);
    let start = std::time::Instant::now();
    parsa_python::PYTHON_GRAMMAR.parse(c);
    eprintln!("elapsed {:?}", start.elapsed()); // note :?

    for _ in 0..10 {
        let c = contents.repeat(10);
        let start = std::time::Instant::now();
        parsa_python::PYTHON_GRAMMAR.parse(c);
        eprintln!("elapsed {:?}", start.elapsed()); // note :?
    }
    Ok(())
}
