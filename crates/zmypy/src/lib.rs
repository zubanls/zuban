use std::env::VarError;
use std::process::ExitCode;
use std::sync::Arc;

use cli_args::Cli;
use colored::Colorize as _;
pub use config::DiagnosticConfig;
pub use zuban_python::Diagnostics;

use config::find_cli_config;
use vfs::{NormalizedPath, SimpleLocalFS, VfsHandler};
use zuban_python::{Project, RunCause};

pub fn run(cli: Cli) -> ExitCode {
    /*
     * TODO renenable this after alpha in some form
    if let Err(err) = licensing::verify_license_in_config_dir() {
        eprintln!("{err}");
        return ExitCode::from(10);
    }
    */

    let current_dir = std::env::current_dir().expect("Expected a valid working directory");
    const CWD_ERROR: &str = "Expected valid unicode in working directory";
    let current_dir = current_dir.into_os_string().into_string().expect(CWD_ERROR);
    with_exit_code(cli, current_dir, None)
}

fn with_exit_code(
    cli: Cli,
    current_dir: String,
    typeshed_path: Option<Arc<NormalizedPath>>,
) -> ExitCode {
    with_diagnostics_from_cli(cli, &current_dir, typeshed_path, |diagnostics, config| {
        let stdout = std::io::stdout();
        for diagnostic in diagnostics.issues.iter() {
            diagnostic
                .write_colored(&mut stdout.lock(), config, &current_dir)
                .unwrap()
        }
        if config.error_summary {
            if diagnostics.error_count() > 0 {
                println!("{}", diagnostics.summary().red().bold());
            } else {
                println!("{}", diagnostics.summary().green().bold());
            }
        }
        ExitCode::from((diagnostics.error_count() > 0) as u8)
    })
    .unwrap_or_else(|err| {
        eprintln!("{err}");
        ExitCode::from(2)
    })
}

pub fn with_diagnostics_from_cli<T>(
    cli: Cli,
    current_dir: &str,
    typeshed_path: Option<Arc<NormalizedPath>>,
    callback: impl FnOnce(Diagnostics, &DiagnosticConfig) -> T,
) -> anyhow::Result<T> {
    tracing::info!("Zuban version {}", env!("CARGO_PKG_VERSION"));
    tracing::info!("Checking in {current_dir}");
    let (mut project, diagnostic_config) =
        project_from_cli(cli, current_dir, typeshed_path, |name| std::env::var(name));
    let diagnostics = project.diagnostics();
    Ok(callback(diagnostics?, &diagnostic_config))
}

fn project_from_cli(
    cli: Cli,
    current_dir: &str,
    typeshed_path: Option<Arc<NormalizedPath>>,
    lookup_env_var: impl Fn(&str) -> Result<String, VarError>,
) -> (Project, DiagnosticConfig) {
    let local_fs = SimpleLocalFS::without_watcher();
    let current_dir = local_fs.unchecked_abs_path(current_dir);
    let mut found = find_cli_config(
        &local_fs,
        current_dir.clone(),
        cli.mypy_options.config_file.as_deref(),
        // Set the default to not mypy compatible, at least for now
        cli.mode(),
    )
    .unwrap_or_else(|err| panic!("Problem parsing Mypy config: {err}"));
    let mut options = found.project_options;
    if let Some(typeshed_path) = typeshed_path {
        options.settings.typeshed_path = Some(typeshed_path);
    }

    options
        .settings
        .try_to_apply_environment_variables(&local_fs, &current_dir, lookup_env_var);

    cli_args::apply_flags(
        &local_fs,
        &mut options,
        &mut found.diagnostic_config,
        cli,
        current_dir,
        found.config_path.as_deref(),
        found.most_probable_base,
    );

    (
        Project::new(Box::new(local_fs), options, RunCause::LanguageServer),
        found.diagnostic_config,
    )
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use clap::Parser as _;

    use super::*;

    fn diagnostics_with_env_lookup(
        cli: Cli,
        directory: &str,
        lookup_env_var: impl Fn(&str) -> Result<String, VarError>,
    ) -> anyhow::Result<Vec<String>> {
        let (mut project, diagnostic_config) = project_from_cli(
            cli,
            directory,
            Some(test_utils::typeshed_path()),
            lookup_env_var,
        );
        let diagnostics = project.diagnostics();
        let mut diagnostics = diagnostics?
            .issues
            .iter()
            .map(|d| {
                let mut s = d.as_string(&diagnostic_config, Some(directory));
                if cfg!(windows) {
                    s = s.replace('\\', "/")
                }
                s
            })
            .collect::<Vec<_>>();
        diagnostics.sort();
        Ok(diagnostics)
    }

    fn diagnostics(cli: Cli, directory: &str) -> Vec<String> {
        diagnostics_with_env_lookup(cli, directory, |_| Err(VarError::NotPresent)).unwrap()
    }

    fn expect_diagnostics_error(cli: Cli, directory: &str) -> String {
        diagnostics_with_env_lookup(cli, directory, |_| Err(VarError::NotPresent))
            .unwrap_err()
            .to_string()
    }

    #[test]
    fn test_diagnostics() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]
            [tool.mypy]
            strict = true

            [file foo.py]
            1()
            def foo(x) -> int: return 1

            [file README]
            Test that readme's are not type checked
            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable  [operator]";
        assert_eq!(
            d(),
            vec![
                NOT_CALLABLE.to_string(),
                "foo.py:2: error: Function is missing a type annotation for one or more arguments  [no-untyped-def]"
                    .to_string()
            ]
        );

        test_dir.remove_file("pyproject.toml");

        assert_eq!(d(), vec![NOT_CALLABLE.to_string()]);
    }

    #[test]
    fn test_pyproject_should_be_ignored_if_no_relevant_entry() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]

            [file setup.cfg]
            [mypy]
            exclude = "foo.py"

            [file foo.py]
            1()
            def foo(x: str) -> int: return 1
            [file bar.py]
            def bar(x) -> None: ...
            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        const NOT_CALLABLE: &str = "foo.py:1: error: \"int\" not callable  [operator]";

        let empty: [&str; _] = [];
        assert_eq!(d(), empty);

        test_dir.write_file("pyproject.toml", "[tool.mypy]");

        assert_eq!(d(), [NOT_CALLABLE]);

        test_dir.write_file("pyproject.toml", "[tool.zuban]");
        assert_eq!(d(), empty);

        // The Zuban config can overwrite mypy settings.
        test_dir.write_file(
            "pyproject.toml",
            "[tool.zuban]\ndisallow_untyped_defs = true",
        );
        const MISSING_ANNOTATION: &str = "bar.py:1: error: Function is missing a type \
                                          annotation for one or more arguments  [no-untyped-def]";
        assert_eq!(d(), [MISSING_ANNOTATION]);

        // Using --config-file should disable all other config files and only use the one
        // specified.
        assert_eq!(
            diagnostics(
                Cli::parse_from(vec!["", "--config-file", "pyproject.toml"]),
                test_dir.path()
            ),
            [MISSING_ANNOTATION, NOT_CALLABLE]
        );

        // If both the zuban config and the mypy section are available in pyproject.toml, that file
        // overwrites everything else.
        test_dir.write_file(
            "pyproject.toml",
            "[tool.zuban]\ndisallow_untyped_defs = true\n[tool.mypy]",
        );
        assert_eq!(d(), [MISSING_ANNOTATION, NOT_CALLABLE]);

        // mypy.ini doesn't change that.
        test_dir.write_file("mypy.ini", "[mypy]\nexclude = \"foo.py\"");
        assert_eq!(d(), [MISSING_ANNOTATION, NOT_CALLABLE]);
    }

    #[test]
    fn test_path_argument() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"

            [file foo.py]
            1()

            [file bar.py]
            1()

            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        const NOT_CALLABLE_FOO: &str = "foo.py:1: error: \"int\" not callable  [operator]";
        const NOT_CALLABLE_BAR: &str = "bar.py:1: error: \"int\" not callable  [operator]";
        // Relative paths
        assert_eq!(
            d(&["", "foo.py", "bar.py"]),
            vec![NOT_CALLABLE_BAR.to_string(), NOT_CALLABLE_FOO.to_string()]
        );
        assert_eq!(d(&["", "foo.py"]), vec![NOT_CALLABLE_FOO.to_string(),]);
        // Absolute path
        let foo_path = Path::new(test_dir.path()).join("foo.py");
        assert_eq!(
            d(&["", foo_path.to_str().unwrap()]),
            vec![NOT_CALLABLE_FOO.to_string(),]
        );

        // Now set a default path
        test_dir.write_file("mypy.ini", "[mypy]\nfiles = foo.py");
        assert_eq!(d(&[""]), vec![NOT_CALLABLE_FOO.to_string(),]);
        assert_eq!(d(&["", "bar.py"]), vec![NOT_CALLABLE_BAR.to_string(),]);
    }

    #[test]
    fn test_environment() {
        logging_config::setup_logging_for_tests();
        // We intentionally also test that dirs with dashes are also checked.
        let fixture = if cfg!(windows) {
            r#"
            [file venv/Scripts/python.exe]

            [file venv/site-packages/foo.py]

            [file venv/site-packages/bar.py]
            1()

            [file m.py]
            import foo

            [file test-dir/n.py]
            import foo
            "#
        } else {
            r#"
            [file venv/bin/python]

            [file venv/lib/python3.12/site-packages/foo.py]

            [file venv/lib/python3.12/site-packages/bar.py]
            1()

            [file venv/src/baz/baz/__init__.py]
            # Installing with pip install -e works similar to this
            my_baz = 1

            [file m.py]
            import foo

            [file test-dir/n.py]
            import foo
            "#
        };
        let test_dir = test_utils::write_files_from_fixture(fixture, false);
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        let err = "error: Cannot find implementation or library stub for module named \"foo\"  [import-not-found]";
        // No venv information should fail to import
        assert_eq!(
            d(&[""]),
            [format!("m.py:1: {err}"), format!("test-dir/n.py:1: {err}"),]
        );
        // venv information via --python-executable should work
        let empty: [&str; _] = [];
        assert_eq!(d(&["", "--python-executable", "venv/bin/python"]), empty);

        // venv information via $VIRTUAL_ENV
        let ds = diagnostics_with_env_lookup(Cli::parse_from([""]), test_dir.path(), |name| {
            match name == "VIRTUAL_ENV" {
                true => Ok("venv".to_string()),
                false => Err(VarError::NotPresent),
            }
        });
        assert_eq!(ds.unwrap(), empty);
    }

    #[test]
    fn test_files_glob() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file foo/bar/mod1.py]
            1()

            [file foo/mod2.py]
            1()

            [file mod3.py]
            1()

            [file mypy.ini]
            [mypy]
            files = foo/*.py
            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());
        let expect_not_found = |cli_args: &[&str]| {
            expect_diagnostics_error(Cli::parse_from(cli_args), test_dir.path().into())
        };

        let err1 = "foo/bar/mod1.py:1: error: \"int\" not callable  [operator]";
        let err2 = "foo/mod2.py:1: error: \"int\" not callable  [operator]";
        let err3 = "mod3.py:1: error: \"int\" not callable  [operator]";

        assert_eq!(d(&[""]), [err2]);

        assert_eq!(d(&["", "foo/**/mod[1-9].py"]), [err1, err2]);
        assert_eq!(d(&["", "**/*.py"]), [err1, err2, err3]);
        assert_eq!(d(&["", "**/mod2.py"]), [err2]);
        assert_eq!(d(&["", "**/"]), [err1, err2, err3]);
        assert_eq!(d(&["", "**/mod?.py"]), [err1, err2, err3]);
        assert_eq!(d(&["", "*.py"]), [err3]);
        assert_eq!(d(&["", "foo"]), [err1, err2]);
        assert_eq!(d(&["", "./foo"]), [err1, err2]);
        assert_eq!(d(&["", "does-not-exist/../foo"]), [err1, err2]);
        // Same file twice
        assert_eq!(d(&["", "foo", "foo/mod2.py"]), [err1, err2]);

        expect_not_found(&["", "foo", "undefined-path"]);
        if cfg!(windows) {
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path"]),
                r"No Python files found to check for C:\foo\zuban\undefined-path"
            );
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path/*/baz/*"]),
                r"No Python files found to check in C:\foo\zuban\undefined-path\*\baz\*"
            );
        } else {
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path"]),
                "No Python files found to check for /foo/zuban/undefined-path"
            );
            assert_eq!(
                expect_not_found(&["", "/foo/zuban/undefined-path/*/baz/*"]),
                "No Python files found to check in /foo/zuban/undefined-path/*/baz/*"
            );
        }
    }

    #[test]
    fn test_files_relative_paths() {
        logging_config::setup_logging_for_tests();
        let mut project_options = config::ProjectOptions::mypy_default();
        let local_fs = SimpleLocalFS::without_watcher();
        let current_dir = local_fs.unchecked_abs_path("/a/b");
        let mut cli = Cli::parse_from([""]);
        cli.mypy_options.files = vec![
            "/a/b/baz.py".to_string(),
            "bla.py".to_string(),
            "/other/".to_string(),
            "/another".to_string(),
            "blub/bla/".to_string(),
            "blub/baz".to_string(),
            "blub/../not_in_blub".to_string(),
        ];
        cli_args::apply_flags(
            &local_fs,
            &mut project_options,
            &mut DiagnosticConfig::default(),
            cli,
            current_dir.clone(),
            Some(current_dir.as_ref()),
            current_dir.clone(),
        );
        let files: Vec<&str> = project_options
            .settings
            .files_or_directories_to_check
            .iter()
            .map(|p| p.as_str())
            .collect();
        if cfg!(target_os = "windows") {
            assert_eq!(
                files,
                vec![
                    r"\a\b\baz.py",
                    r"\a\b\bla.py",
                    r"\other",
                    r"\another",
                    r"\a\b\blub\bla",
                    r"\a\b\blub\baz",
                    r"\a\b\not_in_blub",
                ]
            )
        } else {
            assert_eq!(
                files,
                vec![
                    "/a/b/baz.py",
                    "/a/b/bla.py",
                    "/other",
                    "/another",
                    "/a/b/blub/bla",
                    "/a/b/blub/baz",
                    "/a/b/not_in_blub",
                ]
            )
        }
    }

    #[test]
    fn test_relative_dirs_in_output() {
        logging_config::setup_logging_for_tests();
        let fixture = format!(
            r#"
            [file pyproject.toml]
            [tool.zuban]
            [file folder1/m1.py]
            from folder2 import m2
            1()
            [file folder2/m2.py]
            from folder1 import m1
            ""()
            "#
        );
        let test_dir = test_utils::write_files_from_fixture(&fixture, false);
        let m1 = r#"m1.py:2: error: "int" not callable  [operator]"#;
        let m2 = r#"../folder2/m2.py:2: error: "str" not callable  [operator]"#;
        let all_issues = [m2, m1];

        let dir = &format!("{}/folder1", test_dir.path());
        let ds = diagnostics(Cli::parse_from([""]), dir);
        // By default within a subfolder we still show all issues
        assert_eq!(ds, all_issues);

        // List all diagnostics, not just current file for ..
        let ds = diagnostics(Cli::parse_from(["", ".."]), dir);
        assert_eq!(ds, all_issues);

        // List only current dir diagnostics, for .
        let ds = diagnostics(Cli::parse_from(["", "."]), dir);
        assert_eq!(ds, [m1]);

        // List only m2 diagnostics
        let ds = diagnostics(Cli::parse_from(["", "../folder2"]), dir);
        assert_eq!(ds, [m2]);
        let ds = diagnostics(Cli::parse_from(["", "../folder2/m2.py"]), dir);
        assert_eq!(ds, [m2]);
    }

    #[test]
    fn correct_exit_code() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file with_note.py]
            reveal_type(1)

            [file empty.py]

            [file with_error.py]
            1()
            "#,
            false,
        );
        let c = |cli| {
            with_exit_code(
                cli,
                test_dir.path().into(),
                Some(test_utils::typeshed_path()),
            )
        };
        assert_eq!(c(Cli::parse_from(["", "with_note.py"])), ExitCode::SUCCESS);
        assert_eq!(c(Cli::parse_from(["", "empty.py"])), ExitCode::SUCCESS);
        assert_eq!(c(Cli::parse_from(["", "with_error.py"])), ExitCode::FAILURE);
    }

    #[test]
    fn no_python_files() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file foo/no_py_ending]
            1()
            "#,
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());
        let err = |cli_args: &[&str]| {
            expect_diagnostics_error(Cli::parse_from(cli_args), test_dir.path())
        };

        assert_eq!(
            d(&["", "foo/no_py_ending"]),
            ["foo/no_py_ending:1: error: \"int\" not callable  [operator]",]
        );
        assert!(err(&["", "foo/"]).starts_with("No Python files found to check for"));
        assert_eq!(err(&[""]), "No Python files found to check");
    }

    #[test]
    fn test_pyproject_with_mypy_config_dir_env_var() {
        // From https://github.com/zubanls/zubanls/issues/3
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file pyproject.toml]
            [project]
            name = "hello_zuban"
            version = "0.1.0"

            requires-python = ">= 3.12"
            dependencies = []

            [project.scripts]
            hello-zuban = "hello_zuban:entry_point"

            [tool.mypy]
            mypy_path = "$MYPY_CONFIG_FILE_DIR/src"
            files = ["$MYPY_CONFIG_FILE_DIR/src"]
            strict = true

            [file src/hello_zuban/__init__.py]
            from hello_zuban.hello import X
            from src.hello_zuban.hello import Z

            x = X()

            [file src/hello_zuban/hello.py]
            Z = 1
            class X: pass
            1()

            "#,
            false,
        );
        let d = || diagnostics(Cli::parse_from(vec![""]), test_dir.path());

        assert_eq!(
            d(),
            ["src/hello_zuban/hello.py:3: error: \"int\" not callable  [operator]"]
        );
    }

    #[test]
    fn test_editable_source() {
        logging_config::setup_logging_for_tests();
        // We intentionally also test that dirs with dashes are also checked.
        let test_dir = test_utils::write_files_from_fixture(
            if cfg!(windows) {
                r#"
                [file venv/bin/python]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/Lib/site-packages/frompth.pth]
                ../../..
                ../../frompth
                .

                [file venv/frompth/my_frompth/__init__.py]
                x = 1
                [file venv/frompth/my_frompth/py.typed]

                [file venv/Lib/site-packages/foo.py]

                [file venv/src/baz/baz/__init__.py]
                # Installing with pip install -e works similar to this
                my_baz = 1

                [file venv/src/baz/baz/py.typed]

                [file m.py]
                from typing import assert_type
                import foo
                from baz import my_baz
                reveal_type(my_baz)

                from my_frompth import x
                assert_type(x, int)
                "#
            } else {
                r#"
                [file venv/bin/python]

                [file venv/pyvenv.cfg]
                include-system-site-packages = false
                version = 3.12.3

                [file venv/lib/python3.12/site-packages/frompth.pth]
                # This adds the base path again, which should not recurse
                ../../../..
                ../../../frompth
                # This recurses with the same dir, should not cause a crash
                .

                [file venv/frompth/my_frompth/__init__.py]
                x = 1
                [file venv/frompth/my_frompth/py.typed]
                [file venv/frompth/venv.pth]
                # Introduce a recursion that should cause no problems
                ../lib/python3.12/site-packages

                [file venv/lib/python3.12/site-packages/foo.py]

                [file venv/src/baz/baz/__init__.py]
                # Installing with pip install -e works similar to this
                my_baz = 1

                [file venv/src/baz/baz/py.typed]

                [file m.py]
                from typing import assert_type
                import foo
                from baz import my_baz
                reveal_type(my_baz)

                from my_frompth import x
                assert_type(x, int)

                "#
            },
            false,
        );
        let d = |cli_args: &[&str]| diagnostics(Cli::parse_from(cli_args), test_dir.path());

        assert_eq!(
            d(&["", "--python-executable", "venv/bin/python"]),
            ["m.py:4: note: Revealed type is \"builtins.int\""]
        );

        assert_eq!(
            d(&[""]),
            ["m.py:4: note: Revealed type is \"builtins.int\""]
        );
    }

    #[test]
    fn test_pythonpath() {
        logging_config::setup_logging_for_tests();

        let test_dir = test_utils::write_files_from_fixture(
            r#"
                [file pkg1/bar.py]
                import bar
                import pkg1
                import base
                import doesnotexist
                import baz

                [file pkg2/baz.py]

                [file base.py]

                [file main.py]
                import bar
                import pkg1
                import base
                import doesnotexist
                import baz
                "#,
            false,
        );

        let pth = |dir: &str| {
            Path::new(test_dir.path())
                .join(dir)
                .into_os_string()
                .into_string()
                .unwrap()
        };

        for (var, value) in [
            ("PYTHONPATH", format!("{}:{}", pth("pkg1"), pth("pkg2"))),
            ("MYPYPATH", format!("{}:{}", pth("pkg1"), pth("pkg2"))),
        ] {
            let d = |file: &str| {
                diagnostics_with_env_lookup(Cli::parse_from(&["", file]), test_dir.path(), |s| {
                    match s {
                        _ if s == var => Ok(value.clone()),
                        _ => Err(VarError::NotPresent),
                    }
                })
                .unwrap()
            };
            assert_eq!(
                d("main.py"),
                ["main.py:4: error: Cannot find implementation or library \
                     stub for module named \"doesnotexist\"  [import-not-found]"]
            );
            assert_eq!(
                d("pkg1/bar.py"),
                [
                    "pkg1/bar.py:4: error: Cannot find implementation or library \
                     stub for module named \"doesnotexist\"  [import-not-found]"
                ]
            );
        }
    }

    #[test]
    fn test_gitignore() {
        logging_config::setup_logging_for_tests();
        let test_dir = test_utils::write_files_from_fixture(
            r#"
            [file m.py]
            1()
            [file n.py]
            1()
            [file .gitignore]
            n.py
            "#,
            false,
        );
        let diagnostics = diagnostics(Cli::parse_from([""]), test_dir.path());

        assert_eq!(
            diagnostics,
            ["m.py:1: error: \"int\" not callable  [operator]"]
        );
    }

    #[test]
    fn test_read_file_only_once() {
        logging_config::setup_logging_for_tests();
        for mypy_path in ["['src/inner', 'src']", "['src', 'src/inner']"] {
            let fixture = format!(
                r#"
            [file pyproject.toml]
            [tool.zuban]
            mypy_path = {mypy_path}

            [file src/inner/m1.py]
            import m2
            from inner.m2 import C
            import src

            a: m2.C = C()
            b: C = m2.C()
            c: C = C()
            d: m2.C = m2.C()

            e: src.inner.m2.C = C()

            wrong1: src.inner.m2.C = 1

            [file src/inner/m2.py]
            class C: ...
            "#
            );
            let test_dir = test_utils::write_files_from_fixture(&fixture, false);
            let diagnostics = diagnostics(Cli::parse_from([""]), test_dir.path());

            assert_eq!(
                diagnostics,
                [
                    "src/inner/m1.py:12: error: Incompatible types in assignment (expression \
                     has type \"int\", variable has type \"C\")  [assignment]"
                ]
            );
        }
    }
}
