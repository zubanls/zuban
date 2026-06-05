use serial_test::parallel;
use zubanls::DisplayStatusRequest;

use crate::support::Project;

#[test]
#[parallel]
fn test_status() {
    let server = Project::with_fixture(
        r#"
        [file pyproject.toml]
        [tool.mypy]
        exclude = ["bar.py"]

        [file foo.py]

        [file bar.py]

        "#,
    )
    .into_server();

    let check = |for_file| {
        let status = server.request::<DisplayStatusRequest>(for_file);
        assert_eq!(status.version, 1);
        assert!(status.zuban_version.len() >= 5);
        assert!(!status.zuban_path.is_empty());
        assert!(status.type_checking_enabled);
        assert_eq!(status.mode, "default");
        status
    };

    let foo_py = server.doc_id("foo.py");
    let bar_py = server.doc_id("bar.py");

    check(foo_py);
    check(bar_py);
}
