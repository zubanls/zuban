#!/usr/bin/env bash
set -eu -o pipefail -x

pip install zuban --no-index --find-links dist/ --force-reinstall
zuban --help
