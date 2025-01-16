use std::path::PathBuf;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(version, about)]
struct Cli {
    /// Subcommands
    #[command(subcommand)]
    command: Subcommands,
}

#[derive(Subcommand)]
enum Subcommands {
    /// Verifies a license file in the default config place or a given path
    Verify {
        #[arg()]
        path: Option<PathBuf>,
    },
    Create {
        #[arg(long)]
        name: String,
        #[arg(long)]
        email: String,
        #[arg(long)]
        company: String,
        // Just use 366, even if that's technically wrong, it is ok all the time.
        #[arg(long, default_value_t = 366)]
        days: u64,
        #[arg(long)]
        write: bool,
    },
    HexToRustByteLiterals {
        hex: String,
    },
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().command {
        Subcommands::Verify { path } => {
            let is_ok = match &path {
                Some(path) => licensing::verify_license_in_path(path),
                None => licensing::verify_license_in_config_dir(),
            };
            let path = path.unwrap_or(licensing::path_for_license());
            if is_ok? {
                println!("The license in {path:?} is valid");
            } else {
                anyhow::bail!("The license in {path:?} has an invalid signature");
            }
        }
        Subcommands::Create {
            name,
            email,
            company,
            days,
            write,
        } => {
            let jsonified = licensing::create_license(name, email, company, days)?;
            if write {
                let path = licensing::path_for_license();
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent)?;
                }
                std::fs::write(path, jsonified)?;
            } else {
                println!("{}", jsonified);
            }
        }
        Subcommands::HexToRustByteLiterals { hex } => {
            let bytes = licensing::hex_string_key_to_bytes(hex)?;
            for &byte in bytes.iter() {
                print!("{byte}, ");
            }
            print!("\n");
        }
    }
    Ok(())
}
