use serial_test::parallel;
use zubanls::DisplayStatusRequest;

use crate::connection::Connection;

#[test]
#[parallel]
fn test_status() {
    let con = Connection::initialized(&["/foo/bar"], None, true, None);
    let status = con.request::<DisplayStatusRequest>(());
    assert_eq!(status.display_version, 1);
    assert!(status.zuban_version.len() >= 5);
    assert!(!status.zuban_path.is_empty());
    assert!(status.type_checking_enabled);
    assert_eq!(status.mode, "default");
    con.shutdown_and_exit()
}
