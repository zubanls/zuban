#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

BASE_DIR="../../.."
WORKSPACE_TOML="$BASE_DIR/Cargo.toml"
ZUBAN_TOML="$BASE_DIR/crates/zuban/Cargo.toml"

if [[ -z "${1:-}" ]]; then
  echo "Error: Needs at least one argument, like 'build.sh develop'!"
  exit 1
fi

cargo install cargo-about || true
cargo about generate -o licenses.html about.hbs --fail --manifest-path "$WORKSPACE_TOML" --offline


maturin publish --ignore-rust-version --no-sdist
