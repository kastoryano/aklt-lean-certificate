# Verification output

`./scripts/check.sh` creates `build.log` and `axioms.log` here.
These files are generated locally and are not part of the proof sources.
The script fails if the build fails, an expected axiom report is missing,
or a report uses an axiom outside the three permitted standard foundations.

See [STATUS.md](../STATUS.md) for the verification performed before publication.
