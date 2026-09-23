#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
if ! command -v lake >/dev/null 2>&1; then
  echo 'Lake was not found. Install Lean/elan: https://lean-lang.org/install/' >&2
  exit 1
fi
exec lake "$@"
