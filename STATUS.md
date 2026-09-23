# Verification status

The original scalar certificate completed its build and all 123 recursive
axiom reports on 21 September 2026.

The publication package was checked on **23 September 2026**, on macOS ARM64:

- All 495 Lean source files are byte-for-byte identical to the completed
  certificate, including `RootedKP.lean` and `Audit.lean`.
- The package pins Lean `v4.34.0` and mathlib commit
  `5ed2965256430c3649e86755f9576b54eca72435`, with the same transitive dependencies.
- The default Lake build passed (2441 jobs), and all **123 recursive axiom
  reports passed** using only `propext`, `Classical.choice`, and `Quot.sound`.

This packaging check reused the existing verified project and dependency
compilation caches; it was not a new full cold build. Those caches and the
local toolchain are excluded from the repository. The public build setup
uses pinned Git dependencies and the compiler selected by `lean-toolchain`.

The included Linux workflow has **not yet run on GitHub**. After publication,
start **Verify Lean certificate** from the repository's Actions tab. Its first
run independently compiles the project and audits the resulting declarations.

The final declarations in `RootedKP.AKLT` are:

- `uniformKP_certified`: the model-specific KP condition.
- `edge_root_mass_certified`: the per-edge root mass is at most `7/10`.
- `uniform_root_mass_certified`: a uniform finite per-edge bound exists.
- `scalar_bound_certified`: the cut-rooted heap sum is at most `(7/10) * cut.card`.
- `rooted_summability_certified`: uniform summability over all specified rectangles.

The certificate covers its geometric and counting inputs. It does not
formalize the tensor-network reduction or the full spectral-gap argument.
