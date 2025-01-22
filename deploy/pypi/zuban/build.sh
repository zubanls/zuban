#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

BASE_DIR="../../.."
WORKSPACE_TOML="$BASE_DIR/Cargo.toml"

cargo install cargo-about
cargo about generate -o licenses.html about.hbs --fail --manifest-path "$WORKSPACE_TOML" --offline

maturin publish --ignore-rust-version --no-sdist
