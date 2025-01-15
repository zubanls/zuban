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
    Verify {
        /// Verify
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
}

fn main() -> anyhow::Result<()> {
    match Cli::parse().command {
        Subcommands::Verify { path } => {
            let is_ok = match &path {
                Some(path) => licensing::verify_license_in_path(path),
                None => licensing::verify_license_in_config_dir(),
            };
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
                std::fs::write(licensing::path_for_license(), jsonified)?;
            } else {
                println!("{}", jsonified);
            }
        }
    }
    Ok(())
}
