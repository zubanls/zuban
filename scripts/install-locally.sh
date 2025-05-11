#!/usr/bin/env bash 
set -eu -o pipefail 
                    
cd "$(dirname "$0")"
rm ../target/wheels/*
cd ../deploy/pypi/zuban

maturin build --release

pip install ../../../target/wheels/zuban-*.whl --force-reinstall --break-system-packages
