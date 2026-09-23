import RootedKP.ShortRootCatalog
import RootedKP.ShortRootPruned

/-! A complete finite counter for every normalized short root. The finite start
window is proved from the root coordinates, and the final inequality transports
any finite family of actual corner traversals into this counter. Numerical
maxima over the root catalog remain a separate certificate. -/
namespace RootedKP.ShortRootRepresentatives
open Honeycomb BoundaryCharts BoundaryCounts Enumeration LoopCounts ShortRootCharts
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 2000
attribute [local irreducible] ShortRootCharts.starts

/-- Bounds sufficient to control both infinite boundary rays. -/
def RootFits (root : Finset Vertex) : Prop :=
  ∀ v ∈ root, qCoord v ≤ 20 ∧ -20 ≤ rCoord v

theorem extends_rootFits {n : ℕ} (hn : n ≤ 6) {start : Vertex} {trail : List Vertex}
    (hs : start ∈ anchors) (he : Extends (next .corner) n [start] trail) :
    RootFits trail.toFinset := by
  intro v hv
  have hv' := List.mem_toFinset.mp hv
  have hq := extends_member_height .corner heightQ heightQ_lipschitz he hv'
  have hr := extends_member_height .corner heightR heightR_lipschitz he hv'
  have ha := (mem_anchors start).mp hs
  cases start <;> cases v <;> simp only [qCoord, rCoord, heightQ, heightR] at * <;> omega

theorem catalog_start_bound {root : Finset Vertex} (hr : RootFits root)
    {n : ℕ} (hn : n ≤ 20) {start : Vertex} {trail : List Vertex}
    (hs : Leaf .corner start) (he : Extends (next .corner) n [start] trail)
    (hit : hitsRoot root trail) : start ∈ starts 62 := by
  obtain ⟨v, hv, hvt⟩ := hit
  have hq := extends_member_height .corner heightQ heightQ_lipschitz he hvt
  have hR := extends_member_height .corner heightR heightR_lipschitz he hvt
  have hvb := hr v hv
  have vq : heightQ v ≤ 41 := by cases v <;> simp_all [heightQ, qCoord] <;> omega
  have vr : -40 ≤ heightR v := by cases v <;> simp_all [heightR, rCoord] <;> omega
  have hs' := (leafCode_iff .corner start).mpr hs
  change upperLeaf start ∨ leftLeaf start at hs'
  unfold starts
  rcases hs' with hu | hl
  · cases start with
    | b q r => exact False.elim hu
    | a q r =>
      obtain ⟨hq0, rfl⟩ := hu
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(q + 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        simp only [heightQ] at hq vq
        have hcast := Int.toNat_of_nonneg (show 0 ≤ q + 1 by omega)
        omega
      · have hcast := Int.toNat_of_nonneg (show 0 ≤ q + 1 by omega)
        congr 1
        omega
  · cases start with
    | a q r => exact False.elim hl
    | b q r =>
      obtain ⟨rfl, hr0⟩ := hl
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(-r).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        simp only [heightR] at hR vr
        have hcast := Int.toNat_of_nonneg (show 0 ≤ -r by omega)
        omega
      · have hcast := Int.toNat_of_nonneg (show 0 ≤ -r by omega)
        congr 1
        omega

@[irreducible] def catalogPaths (root : Finset Vertex) (n : ℕ) : Finset (List Vertex) :=
  (starts 62).biUnion (pathsFrom root n)

theorem mem_catalogPaths_iff {root : Finset Vertex} (hr : RootFits root)
    {n : ℕ} (hn : n ≤ 20) (trail : List Vertex) :
    trail ∈ catalogPaths root n ↔ Traversal root n trail := by
  simp only [catalogPaths, pathsFrom, Finset.mem_biUnion, Finset.mem_filter, mem_extensions_iff]
  constructor
  · rintro ⟨start, hs, he, ha⟩
    exact ⟨start, starts_are_leaves hs, he, ha⟩
  · rintro ⟨start, hs, he, ha⟩
    exact ⟨start, catalog_start_bound hr hn hs he ha.2, he, ha⟩

/-- Executable counter, using the independently proved endpoint pruning. -/
def catalogCount (root : Finset Vertex) (n : ℕ) : ℕ :=
  ∑ start ∈ starts 62, prunedCount .corner (accepts root start)
    (endpointPossible .corner) n [start]

theorem catalogCount_eq_card (root : Finset Vertex) (n : ℕ) :
    catalogCount root n = (catalogPaths root n).card := by
  unfold catalogCount catalogPaths
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro start _
    rw [prunedCount_eq _ _ _ (accepted_endpoint_possible root start),
      BoundaryCounts.fastCount_eq, acceptedCount_eq_card]
    rfl
  · intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro trail htu htv
    have heu := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp htu).1
    have hev := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp htv).1
    have : [u] = [v] := (extends_drop heu).symm.trans (extends_drop hev)
    exact hne (List.cons.inj this).1

/-- Complete reduction of short-root path counts to a finite, executable counter.
The anchor bounds hold for every leaf or vertex incident to a chart edge. -/
theorem short_root_count_le {ell n : ℕ} (hell : ell ≤ 6) (hn : n ≤ 20)
    {anchor : Vertex} {root : List Vertex}
    (hqa : -2 ≤ qCoord anchor) (hra : rCoord anchor ≤ 1)
    (hroot : Extends (next .corner) ell [anchor] root)
    (S : Finset (List Vertex)) (hS : ∀ trail ∈ S, Traversal root.toFinset n trail) :
    S.card ≤ catalogCount (root.map (normalize anchor)).toFinset n := by
  have hnroot : Extends (next .corner) ell [normalize anchor anchor]
      (root.map (normalize anchor)) := by
    simpa using normalize_extends hroot (extends_in_patch (by omega : ell ≤ 27) hroot)
  have hfits := extends_rootFits hell (normalize_anchor_mem hqa hra) hnroot
  rw [catalogCount_eq_card]
  let f := List.map (normalize anchor)
  have hinj : Function.Injective f := List.map_injective_iff.mpr (normalize_injective anchor)
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ (catalogPaths (root.map (normalize anchor)).toFinset n).card := by
      apply Finset.card_le_card
      intro trail ht
      obtain ⟨original, hmem, rfl⟩ := Finset.mem_image.mp ht
      exact (mem_catalogPaths_iff hfits hn _).mpr
        (normalize_intersecting_traversal hell hn hroot (hS original hmem))

end RootedKP.ShortRootRepresentatives
