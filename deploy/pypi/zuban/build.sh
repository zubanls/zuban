#!/usr/bin/env bash
set -eu -o pipefail

cd "$(dirname "$0")"

if [[ -z "${2:-}" ]]; then
  echo "Error: Needs at least two arguments, like 'build.sh 0.0.1 develop'!"
  exit 1
fi

version="$1"
maturin_command="$2"

# Only check if something looks like a version number. This is just an
# assertion, correct version checking should be done somewhere else.
if [[ ! "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+ ]]; then
  echo "Error: '$version' does not seem to be a valid version!"
  exit 1
fi

cargo install cargo-about || true
cargo about generate -o licenses.html about.hbs --fail --manifest-path ../../../Cargo.toml

sed "s/<ZubanVersionTag>/$version/" < pyproject.toml.template > pyproject.toml

maturin "$maturin_command" --ignore-rust-version
