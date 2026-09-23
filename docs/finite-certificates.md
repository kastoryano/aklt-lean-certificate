# Finite short-root certificates

Completed and audited on 2026-09-21: all 378 support certificates and the
combined theorem passed. The default audit checks 123 recursive axiom reports;
see [verification status](../STATUS.md) for the final theorem links and scope.

The finite obligation is `AKLT.ShortPrefixCatalogBounds`. For path roots of
lengths four, five, and six, and loop roots of length six, it bounds every
cumulative prefix of the intersecting boundary-path counts at lengths 3–14.
These are cumulative inequalities: an individual count can exceed the
corresponding table increment without violating the required bound.

The original normalized root catalog has 684 possible starting vertices.
Root supports with identical vertex sets have identical intersection counts.
The four catalogs reduce to 35, 2, 35, and 306 support masks, respectively.
`PathCache/RootsFour.lean`, `RootsFive.lean`, `RootsSix.lean`, and
`RootsLoop.lean` prove coverage of every original root. The loop check is
split by vertex phase and coordinate to keep kernel memory use bounded.

## Preserving the actual paths

`PackedSupports.lean` gives a globally injective code for honeycomb vertices.
A finite support is encoded by setting the corresponding bits of a natural
number. There is no coordinate cutoff in this encoding, and Lean proves
that nonempty bitwise intersection is equivalent to actual vertex overlap.

`CachedPathEnumeration.lean` enumerates admissible simple boundary paths
once per starting leaf and length. It uses the same proved endpoint pruning
and endpoint orientation as the original counter. It retains the outer-list
multiplicity: two paths with the same vertex support still contribute twice.
`PathCache/Start*.lean` checks each proposed cache against that enumerator
by kernel reduction. There are 64 starting leaves and 12 lengths, containing
7,710 paths across all lengths and starts. `PathCache/All.lean` proves that
the assembled counter equals the original `catalogCount`.

For efficient numerical verification, `CodeCache/Start*.lean` represents each
cached support as an ascending list of vertex codes. Every list is proved
sorted and is checked to repack to exactly the original support mask.
`CodeHits.lean` proves correctness of the ordered membership test.
`CodeCache/All.lean` proves that counting these lists, separately at each
starting leaf, gives the same original counter.

## Count witnesses and the final implication

`CountCache/*.lean` supplies a separate closed kernel check for every root
support. Each certificate verifies its root encoding, its exact vector of
12 counts, and all 13 cumulative inequalities, including the empty prefix.
The checks are grouped into small modules so that completed results can be
reused independently. `PathCache/Rows*.lean` assembles the four families.
`CertifiedShortPrefix.lean` combines the row certificates and root coverage
to construct `ShortPrefixCatalogBounds`.

The native exporter, Python, and C++ programs only prepare candidate data.
They supply no axiom or trusted numerical oracle. Every assertion used in
the Lean proof must pass kernel checking; the recursive axiom audit checks
the final theorem's dependencies as well.

Lengths 15–20 use the previously proved conservative geometric envelope
`[647, 7740, 2094, 24662, 6803, 89378]`. All larger lengths use proved
analytic tails. All long-root bounds are also proved. The length-four
coefficient is the weaker proved value `4/5`; `FinalPrefixKP.lean` checks
that it still closes the scalar inequality with the original activities
and cost function. The certificate therefore establishes the desired KP
condition without requiring the original stronger length-four estimate.

`CertifiedKP.lean` applies the completed finite input to obtain KP, the
per-edge root bound `7/10`, and the cut-marked heap bound

\[
\sum_h k_{r(h)}\prod_{\gamma\in h}v_\gamma
\le \frac{7}{10}|\mathcal C|.
\]

The regions, activities, tilt, incompatibility relation, and heaps are the
literal definitions in `Polymers.lean` and `Target.lean`. This certificate
concerns the scalar KP and root-counting argument; the tensor-network
operator reduction is outside its scope.
