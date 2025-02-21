#!/usr/bin/env bash
set -eu -o pipefail -x

cd "$(dirname "$0")"

PRIMER_PROJECTS_DIR="$HOME/tmp/mypy_primer/projects"

if [[ -n "${1-}" ]]; then
    DIRS=$1
else
    DIRS=$(ls "$PRIMER_PROJECTS_DIR" | rg -v '_venv$' | sort | sed -n '/meson/,$p' | rg -v 'core|black')
fi

EXECUTABLE="$(pwd)/../target/debug/zmypy"
TYPESHED_DIR="$(realpath ../typeshed)"
cargo build --bin zmypy ${@:2}

while read DIR; do
    VENV="$PRIMER_PROJECTS_DIR/_${DIR}_venv"
    PTH="$PRIMER_PROJECTS_DIR/$DIR"
    cd "$PTH"
    set +e
    ZUBAN_TYPESHED="$TYPESHED_DIR" RUST_BACKTRACE=1 /usr/bin/time "$EXECUTABLE" -- --python-executable "$VENV/bin/python" "$PTH"
    EXIT_CODE="$?"
    set -e
    # Default "valid" codes, but we want to find panics and other aborts
    if [[ $EXIT_CODE -eq 1 || $EXIT_CODE -eq 0 ]]; then
        echo "Ignored error"
    else
        echo "Error: Command exited with status $EXIT_CODE"
        exit $EXIT_CODE
    fi
done <<< "$DIRS"
