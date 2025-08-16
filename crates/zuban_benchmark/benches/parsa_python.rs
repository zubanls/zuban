use criterion::{criterion_group, criterion_main, Criterion};

use parsa_python_cst::Tree;

fn parse_file(copies: usize) {
    let some_code = utils::dedent(
        r#"
        import os
        def x(a, b, c):
            try:
                return a
            except Exception:
                return [1, 2, 3, 4, 5, 6]
        class C:
            x: int
            y = 1 # type: int
            z: dict[int, list[str]] = {1: ["", r''], 2: [f""" {1} """]}
            def f(self, x: list[str], y: int): ...
    "#,
    );
    assert_eq!(some_code.len(), 262);
    Tree::parse(some_code.repeat(copies).into());
}

fn bench_parser(c: &mut Criterion) {
    c.bench_function("parse big file", |b| b.iter(|| parse_file(1000)));
    c.bench_function("parse small file", |b| b.iter(|| parse_file(1)));
}

// Register the benchmarks
criterion_group!(benches, bench_parser);
criterion_main!(benches);
