#!/usr/bin/env bash
set -eu -o pipefail -x

pip install dist/zuban-*.whl --force-reinstall
zubanls --help
