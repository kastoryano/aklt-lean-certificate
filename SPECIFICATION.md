# Specification of the AKLT scalar certificate

The precise propositions are defined in `RootedKP/Target.lean`. Their final
proofs are assembled in `RootedKP/CertifiedKP.lean`; consult `STATUS.md` for
the current build and audit status.

## Regions and polymers

A face rectangle has integer coordinate bounds with `qmin ≤ qmax` and
`rmin ≤ rmax`. The region is its honeycomb sun with halo radius **200**,
as defined in `Honeycomb.lean` and `Polymers.lean`. The theorem quantifies
over every such rectangle, including arbitrarily large rectangles.

A path polymer is the unoriented edge set of a simple sun path between
distinct boundary leaves. A loop polymer is the unoriented edge set of a
simple sun loop. A realizing traversal is an existence witness, so reversing
a path or rotating the starting point of a loop does not create a new polymer.
The length is the number of edges. Two polymers are incompatible exactly when
their vertex supports overlap; this includes self-incompatibility.

## Activities and KP

With `mu = 1/500`, the activity used throughout the heap sum is

\[
v_\gamma=\begin{cases}
\dfrac56\,3^{1-|\gamma|}e^{|\gamma|/500},&\gamma\text{ a path},\\[3pt]
3^{1-|\gamma|}e^{|\gamma|/500},&\gamma\text{ a loop}.
\end{cases}
\]

The cost is

\[
a(3)=.52,\quad a(4)=.56,\quad a(5)=.66,\quad a(6)=.70,
\qquad a(n)=.17n\quad(n\ge7).
\]

`uniformKP_certified` has the type `UniformKPCondition`, which states

\[
\sum_{\gamma'\not\sim\gamma}v_{\gamma'}e^{a(|\gamma'|)}
\le a(|\gamma|)
\]

for every polymer in every region specified above. The cost appears in
this KP test; it is not an extra factor in the activity used in heap weights.

## Rooted heaps and root counting

Heaps are the actual finite labelled occurrence posets defined by
`Heaps.Heap`, modulo label-preserving order isomorphism. Repeated occurrences
of a polymer label are allowed. A rooted heap has a unique minimum.
Its weight is the product of the activities of all its occurrences.

For an arbitrary finite edge set `cut`, let `k_r` be the number of cut edges
belonging to the root polymer. `scalarSum` sums `k_r` times the heap weight
over all rooted heaps with `k_r > 0`. It is an extended nonnegative sum;
a finite bound therefore establishes convergence.

The explicit conclusions in `CertifiedKP.lean` are

\[
\sum_{\gamma\ni e}v_\gamma e^{a(|\gamma|)}\le\frac7{10}
\quad\text{and}\quad
\sum_h k_{r(h)}\prod_{\gamma\in h}v_\gamma
\le\frac7{10}|\mathrm{cut}|.
\]

The first is `edge_root_mass_certified`; the second is
`scalar_bound_certified`. The root-counting argument applies KP to a proved
six-edge face-loop witness. The bound is uniform in the rectangle and the
choice of finite cut. `rooted_summability_certified` states the corresponding
uniform summability proposition.

This specification concerns the scalar KP and root-counting step. The
operators `rho_boundary`, `E_R`, and `K_z`, and the tensor-network reduction to this
scalar sum, are outside this Lean project.
