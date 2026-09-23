# Relation to the paper's scalar proof

The formal target is the rooted heap summability lemma in
the accompanying manuscript, with the same weights, tilt, and halo radius.
No tensor-network operator theorem is asserted by this project.

## Fixed-root KP: complete

`Heaps.rooted_heap_KP_of_criterion` proves the conclusion of the paper's
abstract rooted KP lemma. The formal proof takes a direct combinatorial
route, avoiding an additional formalization of the cluster-expansion
identity used in the manuscript.

Remove the least occurrence of a rooted heap. Each new minimal occurrence
has a label incompatible with the removed root. Self-incompatibility makes
these minimal labels distinct. Assign every remaining occurrence to the
largest label among its minimal ancestors, using an arbitrary ordering of
the finite polymer set. Each nonempty class is itself a rooted heap.

The classes reconstruct the original dependence order, so this assignment
is injective on heaps modulo label-preserving isomorphism. Its weights
factor exactly. The resulting bound for heaps of size at most `N+1` is

\[
P_p^{N+1}\le v_p\prod_{q\not\sim p}(1+P_q^N).
\]

The KP assumption closes the induction using `1+x <= exp(x)`. Exhausting
all finite sizes proves the infinite heap bound. No recursion, convergence,
or cluster-expansion theorem is supplied as an unproved hypothesis.

## Counting roots through an edge: complete

The paper bounds this sum by counting nonbacktracking paths. The formal
proof uses a shorter argument available in these particular sun regions.

Every edge used by a polymer has a core endpoint. That endpoint belongs to
a halo face, whose six boundary edges form an allowed loop `q`. Every
polymer `p` using the chosen edge meets `q` at that endpoint. Consequently,

\[
\sum_{p\ni e}v_p e^{a(p)}
\le\sum_{p\not\sim q}v_p e^{a(p)}
\le a(q)=7/10.
\]

The existence of this actual face-loop witness is proved in `FaceProbes`;
it is not an additional geometric assumption. If no polymer uses the edge,
the sum is zero. `ProbeRootCounting` then combines this result with the
fixed-root theorem and the exact cut-mark identity to prove

\[
\sum_{h\in\mathscr H_R}k_{r(h)}\prod_{p\in h}v_p
\le (7/10)|\mathcal C|.
\]

The intermediate result assumes the literal model-specific KP condition.
`CertifiedKP.lean` now supplies its proof and obtains the displayed bound
without an additional hypothesis.

## Verifying that AKLT satisfies KP: complete

The arithmetic inequalities have been checked in Lean with conservative
exponential envelopes. The infinite anchored loop envelope uses only
kernel-enumerated lengths through 20 and a proved tail from 22 onwards.
It now transfers to canonical regional loops, every regional edge, and the
full incompatible-loop contribution, without additional hypotheses.
All scalar comparisons used by the final implication are kernel checked.

The regional transfer is now proved for endpoints, short roots, and arbitrary
long roots. All infinite tails and all long-root path lengths are discharged. The three-edge short root is fully certified through length
20. For the other short roots, one fixed normalized representative controls
all the intersecting path families.

The finite computation stops at length 14. For lengths 15–20,
the proved odd/collar bounds give the common short-root envelope
`[647, 7740, 2094, 24662, 6803, 89378]`. Although much larger than the original
counts, its weighted contribution leaves enough margin in every short-root
KP inequality. `ShortPrefixCompletion.lean` proves this arithmetic comparison
and the complete implication from the shorter cumulative prefix.

The width-zero collar also gives the bound `N4 ≤ (4/5) * root.length`.
Path roots are trimmed by their two leaf prongs; loop roots of length at
least seven have length at least ten. The weaker length-four coefficient
still satisfies the long-root scalar inequality with the original activities
and costs, as proved in `FinalPrefixKP.lean`.

`CertifiedShortPrefix.lean` now constructs `ShortPrefixCatalogBounds`.
Every original root is covered by one of 378 support representatives, and
all 378 exact count vectors and cumulative inequalities are checked by the
kernel. The complete path enumerator is shared across roots. Each cached
path retains its multiplicity, and the optimized representation is proved
equivalent to the original vertex-overlap counter. See
[finite-certificate documentation](docs/finite-certificates.md).

`CertifiedKP.lean` combines this finite input with `FinalPrefixKP.lean` to
prove the literal KP condition, the per-edge root bound `7/10`, and uniform
rooted-heap summability. The final scalar theorem takes only a rectangle
and a finite cut as parameters. The default build and all 123 recursive
axiom reports pass using only Lean's standard foundations.
