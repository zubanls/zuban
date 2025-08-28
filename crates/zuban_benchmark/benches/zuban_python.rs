use criterion::{Criterion, criterion_group, criterion_main};

use config::ProjectOptions;
use vfs::PathWithScheme;
use zuban_python::{Mode, Project};

fn check_independent_files(file_count: usize) {
    let some_code = utils::dedent(
        r#"
        def foo(x: int) -> int:
            return x
    "#,
    );
    let mut po = ProjectOptions::default();
    po.settings.typeshed_path = Some(test_utils::typeshed_path());
    let mut project = Project::without_watcher(po, Mode::TypeCheckingOnly);
    for i in 0..file_count {
        let vfs = project.vfs_handler();
        let path = PathWithScheme::with_file_scheme(
            vfs.normalize_rc_path(vfs.unchecked_abs_path(&format!("/bench-test/test{i}.py"))),
        );
        project.store_in_memory_file(path, some_code.clone().into())
    }
}

fn bench_type_checking(c: &mut Criterion) {
    c.bench_function("1 file", |b| b.iter(|| check_independent_files(1)));
    c.bench_function("1000 files", |b| b.iter(|| check_independent_files(1000)));
}

// Register the benchmarks
criterion_group!(benches, bench_type_checking);
criterion_main!(benches);
