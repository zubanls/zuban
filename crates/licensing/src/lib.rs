use std::path::{Path, PathBuf};
use std::str::FromStr;
use std::time::{SystemTime, UNIX_EPOCH};

use ed25519_dalek::{
    ed25519::signature::SignerMut as _, Signature, SigningKey, VerifyingKey, PUBLIC_KEY_LENGTH,
};

const VALID_PUBLIC_KEYS: [[u8; PUBLIC_KEY_LENGTH]; 0] = [];
const CURRENT_LICENSE_VERSION: usize = 1;

#[derive(serde::Serialize, serde::Deserialize)]
struct License {
    name: String,
    email: String,
    company: String,
    valid_from: SystemTime,
    valid_until: SystemTime,
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
        Self {
            name,
            email,
            company,
            valid_from,
            valid_until,
            signature: "".to_string(),
            license_version: CURRENT_LICENSE_VERSION,
        }
    }

    fn to_bytes_message(&self) -> Vec<u8> {
        let t_to_str = |t: &SystemTime| t.duration_since(UNIX_EPOCH).unwrap().as_secs().to_string();
        [
            self.name.as_bytes(),
            b"\n",
            self.email.as_bytes(),
            b"\n",
            self.company.as_bytes(),
            b"\n",
            t_to_str(&self.valid_from).as_bytes(),
            b"\n",
            t_to_str(&self.valid_until).as_bytes(),
            b"\n",
            self.license_version.to_string().as_bytes(),
            b"\n",
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
        self.verify_with_keys(VALID_PUBLIC_KEYS.iter())
    }

    fn verify_with_keys<'x>(
        &self,
        public_keys: impl Iterator<Item = &'x [u8; 32]>,
    ) -> anyhow::Result<bool> {
        for public_key in public_keys {
            let verifying_key = VerifyingKey::from_bytes(public_key).unwrap();
            let wanted_signature = Signature::from_str(&self.signature)?;
            if verifying_key
                .verify_strict(&self.to_bytes_message(), &wanted_signature)
                .is_ok()
            {
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
    utils::config_dir_path().expect("No valid config directory found")
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
    let valid_from = std::time::SystemTime::now();
    const DAY: u64 = 60 * 60 * 24;
    let valid_until = valid_from + std::time::Duration::from_secs(days * DAY);
    let mut license = License::create(name, email, company, valid_from, valid_until);
    let private_key = std::env::var("ZUBAN_PRIVATE_KEY")?;
    //TODO license.sign(private_key);
    Ok(license.to_json())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_signing() {
        const PRIVATE_KEY: [u8; 32] = [
            0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x04, 0x22,
            0x04, 0x20, 0xe0, 0x4f, 0xed, 0xa8, 0xc9, 0x4a, 0xb0, 0xbc, 0x7f, 0x3e, 0x2e, 0xd9,
            0x73, 0xa5, 0x88, 0xf8,
        ];

        let now = std::time::SystemTime::now();
        let mut license = License::create(
            "Dave".to_string(),
            "info@zubanls.com".to_string(),
            "Zuban Company".to_string(),
            now - std::time::Duration::from_secs(3600),
            now + std::time::Duration::from_secs(3600),
        );
        license.sign(&PRIVATE_KEY).unwrap();
        let signing_key = SigningKey::from_bytes(&PRIVATE_KEY);
        let result = license
            .verify_with_keys(std::iter::once(signing_key.verifying_key().as_bytes()))
            .unwrap();
        let last = license.signature.pop().unwrap();
        if last == '4' {
            license.signature.push('3');
        } else {
            license.signature.push('4');
        }
        assert_eq!(result, true);

        let result = license
            .verify_with_keys(std::iter::once(signing_key.verifying_key().as_bytes()))
            .unwrap();
        assert_eq!(result, false);
    }
}
