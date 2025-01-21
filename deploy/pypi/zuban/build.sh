#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

cargo install cargo-about || true
cargo about generate -o licenses.html about.hbs --fail --manifest-path ../../../Cargo.toml

maturin "$1"
