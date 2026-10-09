#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

BASE_DIR="../../.."
WORKSPACE_TOML="$BASE_DIR/Cargo.toml"

# Use --debug to speed up compilation
cargo install --features cli --locked --debug cargo-about --version 0.9.0
cargo about generate -o licenses.html about.hbs --fail --manifest-path "$WORKSPACE_TOML"
