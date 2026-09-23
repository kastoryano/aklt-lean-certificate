#!/usr/bin/env python3
"""Reject missing reports or axioms beyond Lean's standard foundations."""
from pathlib import Path
import re
import sys

project = Path(__file__).resolve().parents[1]
expected = re.findall(r"^#print axioms (\S+)$", (project / "Audit.lean").read_text(), re.M)
report_path = Path(sys.argv[1]) if len(sys.argv) > 1 else project / "audit/axioms.log"
report = report_path.read_text()
found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", report))
for name in re.findall(r"'([^']+)' does not depend on any axioms", report):
    found[name] = ""
allowed = {"propext", "Classical.choice", "Quot.sound"}
errors = []
for name in expected:
    if name not in found:
        errors.append(f"Missing axiom report: {name}")
        continue
    axioms = {s.strip() for s in found[name].split(",") if s.strip()}
    if axioms - allowed:
        errors.append(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
if errors:
    raise SystemExit("\n".join(errors))
print(f"Checked {len(expected)} recursive axiom reports: standard foundations only.")
print("Axiom auditing checks dependencies; consult theorem signatures for assumptions.")
