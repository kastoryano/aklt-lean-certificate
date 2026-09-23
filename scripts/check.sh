#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
command -v python3 >/dev/null 2>&1 || {
  echo 'Python 3 is required for the axiom audit.' >&2
  exit 1
}
mkdir -p audit
echo 'Building the Lean certificate. Progress is written to audit/build.log.'
python3 scripts/build_limited.py > audit/build.log 2>&1 || {
  tail -n 60 audit/build.log
  exit 1
}
echo 'Checking recursive axiom reports.'
./scripts/lake.sh env lean Audit.lean > audit/axioms.log 2>&1 || {
  cat audit/axioms.log
  exit 1
}
python3 scripts/audit_axioms.py audit/axioms.log
echo 'Certificate build and axiom audit passed.'
