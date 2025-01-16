use std::num::ParseIntError;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use ed25519_dalek::{
    ed25519::signature::SignerMut as _, Signature, SigningKey, VerifyingKey, PUBLIC_KEY_LENGTH,
};

const VALID_PUBLIC_KEYS: [[u8; PUBLIC_KEY_LENGTH]; 10] = [
    [
        30, 7, 45, 28, 83, 183, 159, 89, 157, 218, 71, 174, 103, 145, 40, 60, 82, 200, 3, 61, 221,
        232, 202, 124, 111, 246, 187, 220, 237, 81, 229, 64,
    ],
    [
        47, 139, 112, 67, 122, 179, 161, 44, 82, 5, 31, 234, 133, 240, 79, 7, 29, 70, 231, 32, 199,
        78, 106, 177, 172, 140, 231, 239, 89, 160, 141, 62,
    ],
    [
        194, 198, 123, 174, 25, 229, 130, 243, 60, 87, 48, 35, 154, 24, 89, 242, 156, 75, 233, 165,
        255, 2, 202, 179, 51, 16, 200, 125, 205, 74, 152, 72,
    ],
    [
        159, 224, 200, 34, 252, 243, 118, 107, 94, 158, 171, 52, 38, 78, 100, 73, 217, 148, 217,
        239, 224, 176, 44, 190, 226, 65, 82, 218, 210, 88, 55, 205,
    ],
    [
        201, 38, 63, 227, 237, 191, 37, 116, 64, 39, 207, 135, 249, 194, 172, 43, 130, 32, 101,
        236, 143, 129, 102, 172, 114, 229, 135, 156, 186, 125, 92, 218,
    ],
    [
        230, 121, 114, 190, 169, 137, 3, 185, 140, 117, 81, 28, 61, 11, 196, 33, 119, 173, 129,
        231, 97, 5, 254, 68, 36, 245, 201, 177, 180, 41, 92, 86,
    ],
    [
        34, 180, 104, 70, 123, 144, 245, 40, 122, 253, 213, 71, 211, 26, 108, 130, 242, 220, 191,
        5, 73, 249, 59, 124, 218, 129, 39, 251, 196, 240, 34, 135,
    ],
    [
        94, 2, 75, 32, 233, 141, 130, 109, 68, 147, 84, 157, 248, 61, 7, 130, 41, 120, 31, 216, 72,
        219, 153, 47, 63, 221, 177, 112, 80, 215, 20, 132,
    ],
    [
        167, 29, 6, 110, 161, 86, 43, 221, 185, 86, 53, 118, 239, 97, 97, 28, 104, 70, 4, 176, 35,
        227, 94, 106, 203, 211, 134, 17, 13, 202, 199, 169,
    ],
    [
        10, 207, 195, 137, 135, 47, 97, 195, 245, 2, 211, 138, 178, 99, 245, 75, 63, 96, 8, 98,
        110, 67, 103, 55, 138, 191, 173, 79, 191, 254, 243, 186,
    ],
];
const CURRENT_LICENSE_VERSION: usize = 1;

#[derive(serde::Serialize, serde::Deserialize)]
struct License {
    name: String,
    email: String,
    company: String,
    valid_from: u64,
    valid_until: u64,
    license_version: usize,

    signature: String,
}

impl License {
    fn create(
        name: String,
        email: String,
        company: String,
        valid_from: SystemTime,
        valid_until: SystemTime,
    ) -> Self {
        let t_to_int = |t: SystemTime| t.duration_since(UNIX_EPOCH).unwrap().as_secs();
        Self {
            name,
            email,
            company,
            valid_from: t_to_int(valid_from),
            valid_until: t_to_int(valid_until),
            signature: "".to_string(),
            license_version: CURRENT_LICENSE_VERSION,
        }
    }

    fn to_bytes_message(&self) -> Vec<u8> {
        [
            self.name.as_bytes(),
            self.email.as_bytes(),
            self.company.as_bytes(),
            self.valid_from.to_string().as_bytes(),
            self.valid_until.to_string().as_bytes(),
            self.license_version.to_string().as_bytes(),
        ]
        .concat()
    }

    fn sign(&mut self, private_key: &[u8; 32]) -> anyhow::Result<()> {
        let mut signing_key = SigningKey::from_bytes(private_key);
        let signature = signing_key.sign(&self.to_bytes_message());
        self.signature = signature.to_string();
        Ok(())
    }

    fn verify(&self) -> anyhow::Result<bool> {
        self.verify_with_keys(SystemTime::now(), VALID_PUBLIC_KEYS.iter())
    }

    fn verify_with_keys<'x>(
        &self,
        current_time: SystemTime,
        public_keys: impl Iterator<Item = &'x [u8; 32]>,
    ) -> anyhow::Result<bool> {
        for public_key in public_keys {
            let verifying_key = VerifyingKey::from_bytes(public_key).unwrap();
            let wanted_signature = Signature::from_str(&self.signature)?;
            if verifying_key
                .verify_strict(&self.to_bytes_message(), &wanted_signature)
                .is_ok()
            {
                let current_timestamp = current_time
                    .duration_since(UNIX_EPOCH)
                    .expect("Negative timestamps should not be possible")
                    .as_secs();
                if self.valid_from > current_timestamp {
                    anyhow::bail!("The license is not yet valid")
                }
                if self.valid_until < current_timestamp {
                    anyhow::bail!("The license has expired")
                }
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn to_json(&self) -> String {
        assert!(
            !self.signature.is_empty(),
            "A signature should always have been calculated"
        );
        serde_json::to_string(self).unwrap()
    }

    fn from_json(s: &str) -> anyhow::Result<Self> {
        Ok(serde_json::from_str(s)?)
    }
}

pub fn path_for_license() -> PathBuf {
    utils::config_dir_path()
        .expect("No valid config directory found")
        .join("license.json")
}

pub fn verify_license_in_config_dir() -> anyhow::Result<bool> {
    verify_license_in_path(&path_for_license())
}

pub fn verify_license_in_path(path: &Path) -> anyhow::Result<bool> {
    let license_s =
        std::fs::read_to_string(&path).map_err(|err| anyhow::anyhow!("In {:?}: {err}", &path))?;
    let license = License::from_json(&license_s)?;
    license.verify()
}

pub fn create_license(
    name: String,
    email: String,
    company: String,
    days: u64,
) -> anyhow::Result<String> {
    let valid_from = SystemTime::now();
    const DAY: u64 = 60 * 60 * 24;
    let valid_until = valid_from + Duration::from_secs(days * DAY);
    let mut license = License::create(name, email, company, valid_from, valid_until);
    let var = "ZUBAN_SIGNING_KEY";
    let private_key = std::env::var(var).map_err(|err| anyhow::anyhow!("{err}: {var}"))?;
    license.sign(&hex_string_key_to_bytes(private_key)?)?;
    Ok(license.to_json())
}

/// Parses a hex formatted string like "cc:aa:ff:ee", but 32 bytes long.
pub fn hex_string_key_to_bytes(s: String) -> anyhow::Result<[u8; PUBLIC_KEY_LENGTH]> {
    s.split(':')
        .map(|hex_part| u8::from_str_radix(hex_part, 16))
        .collect::<Result<Vec<u8>, ParseIntError>>()?
        .try_into()
        .map_err(|v: Vec<_>| {
            anyhow::anyhow!(
                "Invalid length for key of {}, expected {PUBLIC_KEY_LENGTH}",
                v.len()
            )
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    const PRIVATE_KEY: [u8; 32] = [
        251, 177, 48, 122, 118, 59, 229, 37, 61, 11, 93, 104, 131, 143, 69, 142, 3, 192, 34, 85,
        89, 219, 163, 163, 203, 135, 122, 75, 153, 94, 245, 182,
    ];

    fn license_with_times(from: SystemTime, to: SystemTime) -> License {
        let mut license = License::create(
            "Dave".to_string(),
            "info@zubanls.com".to_string(),
            "Zuban Company".to_string(),
            from,
            to,
        );
        // Successfully validate
        license.sign(&PRIVATE_KEY).unwrap();
        license
    }

    fn license() -> License {
        let now = SystemTime::now();
        license_with_times(
            now - Duration::from_secs(3600),
            now + Duration::from_secs(3600),
        )
    }

    fn verify(license: License, now: SystemTime) -> anyhow::Result<bool> {
        let signing_key = SigningKey::from_bytes(&PRIVATE_KEY);
        license.verify_with_keys(now, std::iter::once(signing_key.verifying_key().as_bytes()))
    }

    #[test]
    fn test_signing() {
        let result = verify(license(), SystemTime::now()).unwrap();
        assert!(result);
    }

    #[test]
    fn test_changed_signature() {
        // Change the signature, which should cause problems
        let mut license = license();
        let last = license.signature.pop().unwrap();
        if last == '4' {
            license.signature.push('3');
        } else {
            license.signature.push('4');
        }
        let result = verify(license, SystemTime::now()).unwrap();
        assert!(!result);
    }

    #[test]
    fn test_changed_values() {
        fn check(change: impl FnOnce(&mut License)) -> bool {
            let mut license = license();
            change(&mut license);
            verify(license, SystemTime::now()).unwrap()
        }
        // Change nothing and it should be valid
        assert!(check(|_| ()));
        // Once changed it should fail, notice the `!`
        assert!(!check(|license| license.name += "F"));
        assert!(!check(|license| license.email = "".to_owned()));
        assert!(!check(|license| license.company = "Plsdontsuck".to_owned()));
        assert!(!check(|license| license.valid_from += 1));
        assert!(!check(|license| license.valid_until += 1));
        assert!(!check(|license| license.license_version += 1));
    }

    #[test]
    fn test_check_valid_timestamps() {
        fn check(from_diff: i64, to_diff: i64) -> Result<bool, String> {
            let now = SystemTime::now();
            let add_to = |diff: i64| match diff.try_into() {
                Ok(add) => now + Duration::from_secs(add),
                Err(_) => now - Duration::from_secs((-diff) as u64),
            };
            let license = license_with_times(add_to(from_diff), add_to(to_diff));
            verify(license, now).map_err(|err| err.to_string())
        }
        // The numbers here are ints that are different from now
        assert_eq!(check(-1, 1), Ok(true));
        assert_eq!(check(-1, -1), Err("The license has expired".to_string()));
        assert_eq!(check(-2, -1), Err("The license has expired".to_string()));
        assert_eq!(check(-1, -2), Err("The license has expired".to_string()));
        assert_eq!(check(1, 1), Err("The license is not yet valid".to_string()));
        assert_eq!(check(1, 2), Err("The license is not yet valid".to_string()));
        assert_eq!(check(2, 1), Err("The license is not yet valid".to_string()));
    }
}
