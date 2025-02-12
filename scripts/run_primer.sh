#!/usr/bin/env bash
set -eu -o pipefail -x

cd "$(dirname "$0")"

PRIMER_PROJECTS_DIR="$HOME/tmp/mypy_primer/projects"

DIRS=$(ls "$PRIMER_PROJECTS_DIR" | rg -v '_venv$' | sort)

EXECUTABLE="$(pwd)/../target/debug/zmypy"
TYPESHED_DIR="$(realpath ../typeshed)"
cargo build --bin zmypy

while read DIR; do
    VENV="$PRIMER_PROJECTS_DIR/_${DIR}_venv"
    PTH="$PRIMER_PROJECTS_DIR/$DIR"
    cd "$PTH"
    ZUBAN_TYPESHED="$TYPESHED_DIR" "$EXECUTABLE" -- --python-executable "$VENV/bin/python" "$PTH"
done <<< "$DIRS"
