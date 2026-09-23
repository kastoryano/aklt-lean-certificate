# AKLT scalar summability: Lean certificate

This repository contains the Lean proof of the scalar rooted-heap summability
estimate used in **Spectral Gap of the Hexagonal AKLT Model via Boundary-State
Factorization**, by Michael J. Kastoryano.

The final theorem proves

\[
\mathscr S_{R(F)}(1/500)\le \frac{7}{10}|\mathcal C|
\]

for every nonempty lattice rectangle `F` and every finite cut `C`, with the
radius-200 honeycomb sun regions, path and loop activities, and compatibility
relation specified in [SPECIFICATION.md](SPECIFICATION.md). This includes
the geometric reductions, finite counts, infinite tails, and rooted-heap
argument. The quantum reduction, boundary-state comparison, and full spectral-gap
argument are outside this formalization.

Start with [the final theorems](RootedKP/CertifiedKP.lean),
[the precise statement](SPECIFICATION.md), and
[the correspondence with the paper](PROOF_MAP.md).

## Verify the certificate

The command-line instructions below use macOS or Linux; Windows users can use
WSL. Install [Lean and its version manager elan](https://lean-lang.org/install/),
Git, and Python 3. No Python packages beyond the standard library are required.
The `lean-toolchain` file selects the required compiler version automatically
when Lean is installed through elan.

Clone the public repository and run the verification scripts:

```sh
git clone https://github.com/kastoryano/aklt-lean-certificate.git
cd aklt-lean-certificate
./scripts/setup.sh
./scripts/check.sh
```

The setup fetches the pinned dependencies and their compiled mathlib cache.
The check builds the project sources, runs `Audit.lean`, and validates every
expected recursive axiom report. Success ends with:

```text
Checked 123 recursive axiom reports: standard foundations only.
Axiom auditing checks dependencies; consult theorem signatures for assumptions.
Certificate build and axiom audit passed.
```

The permitted foundations are `propext`, `Classical.choice`, and `Quot.sound`.
Dependence on a proof placeholder or an extra axiom in any audited declaration
causes failure. Missing reports also cause failure.
Inspect `audit/build.log` and `audit/axioms.log` for the full local results.

### Build resources

The first build performs substantial kernel computations. Dependency downloads
and compiler/build artifacts require several gigabytes of disk space. The check
script limits project-module compilation to two workers by default. Use
`AKLT_BUILD_JOBS=1 ./scripts/check.sh` to reduce concurrent memory use, or increase
the value on a machine with sufficient memory. Later builds reuse the local
`.lake` cache. [STATUS.md](STATUS.md) records the measured publication check.

For an ordinary Lake build without the concurrency-limiting wrapper, run
`lake build`, then `lake env lean Audit.lean` and the Python axiom audit.
The supplied `check.sh` runs all three stages and checks their exit status.

### Optional GitHub verification

The included **Verify Lean certificate** workflow can be started from the
repository's **Actions** tab using **Run workflow**. It performs the same
build and audit on a GitHub-hosted Linux machine and retains the logs as a
downloadable artifact. It is triggered manually, so uploading the repository
does not start a long computation automatically. A successful local run and
a successful GitHub run are recorded separately in [STATUS.md](STATUS.md).

## Pinned environment

- Lean: `leanprover/lean4:v4.34.0`.
- mathlib: commit `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`).
- Transitive dependencies: the exact revisions in `lake-manifest.json`.

The proof sources and generated witness certificates are committed here.
Downloaded toolchains, dependencies, and compiled files are not part of the
repository. The files in `PathCache`, `CodeCache`, and `CountCache` are Lean
source certificates: their proposed data and required equalities are checked
by the kernel. They are required sources, not disposable build caches.
No external enumeration program or unpublished input data is needed to verify
the committed proof. See [the finite-certificate explanation](docs/finite-certificates.md).

## Reading the proof

| File | Role |
| --- | --- |
| [CertifiedKP.lean](RootedKP/CertifiedKP.lean) | Final unconditional scalar theorems. |
| [Target.lean](RootedKP/Target.lean) | Exact target propositions. |
| [Polymers.lean](RootedKP/Polymers.lean) | Regional paths, loops, and activities. |
| [HeapMass.lean](RootedKP/HeapMass.lean) | Abstract rooted-heap summability theorem. |
| [ProbeRootCounting.lean](RootedKP/ProbeRootCounting.lean) | The six-edge-loop argument for the constant `7/10`. |
| [CertifiedShortPrefix.lean](RootedKP/CertifiedShortPrefix.lean) | Assembly of the finite count certificates. |
| [FinalPrefixKP.lean](RootedKP/FinalPrefixKP.lean) | Geometric and arithmetic estimates combined into KP. |
| [Audit.lean](Audit.lean) | Recursive axiom reports and final theorem signatures. |

The main declarations are in the namespace `RootedKP.AKLT`:
`uniformKP_certified`, `edge_root_mass_certified`, `scalar_bound_certified`,
and `rooted_summability_certified`. Intermediate lemmas may state explicit
hypotheses; the final assembly proves the required inputs.

## Citation and license

Please cite the accompanying paper and the specific archived release used.
Citation metadata is in [CITATION.cff](CITATION.cff); a DOI can be added when
the release is archived. All paths in this documentation are relative to
this repository.

The original proof sources and documentation are provided under the
[MIT License](LICENSE). Downloaded dependencies retain their own licenses;
mathlib and Lean are not redistributed in this repository.
