#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
echo 'Checking the pinned Lean toolchain and fetching the mathlib cache.'
./scripts/lake.sh env lean --version
./scripts/lake.sh exe cache get
echo 'Dependencies are ready. Run ./scripts/check.sh to verify the certificate.'
