import RootedKP.ShortRootNormalization
import RootedKP.Polymers
import Mathlib.Data.Int.Interval

/-!
A complete finite catalog of short corner-chart roots, modulo local translation.
The catalog uses exact simple traversals and then canonical unoriented edge sets.
Reversal/rotation duplicates are removed by Finset.image; no numerical maximum
is asserted in this module. ShortRootNormalization proves that all paths of
length≤20 intersecting a root are preserved by the same translation.
-/
namespace RootedKP.ShortRootRepresentatives
open Honeycomb BoundaryCharts BoundaryCounts Enumeration LoopCounts AKLT

set_option maxHeartbeats 0
set_option maxRecDepth 2000

/-- A conservative finite anchor box including both corner rays and the bulk. -/
@[irreducible] def anchors : Finset Vertex :=
  (Finset.Icc (-2 : ℤ) 16).biUnion fun q =>
    (Finset.Icc (-16 : ℤ) 1).biUnion fun r => {.a q r, .b q r}

theorem mem_anchors (v : Vertex) : v ∈ anchors ↔
    -2 ≤ qCoord v ∧ qCoord v ≤ 16 ∧ -16 ≤ rCoord v ∧ rCoord v ≤ 1 := by
  cases v <;> simp [anchors, qCoord, rCoord] <;> omega

theorem normalize_anchor_mem {anchor : Vertex}
    (hq : -2 ≤ qCoord anchor) (hr : rCoord anchor ≤ 1) :
    normalize anchor anchor ∈ anchors := by
  rw [mem_anchors]
  cases anchor <;> simp only [normalize, translate, qCoord, rCoord] at *
  all_goals simp only [min_def, max_def]; split_ifs <;> omega

theorem leaf_anchor_bounds {v : Vertex} (hv : Leaf .corner v) :
    -2 ≤ qCoord v ∧ rCoord v ≤ 1 := by
  rw [← leafCode_iff] at hv
  cases v <;> simp_all [leafCode, upperLeaf, leftLeaf, qCoord, rCoord] <;> omega

theorem adjacent_anchor_bounds {u v : Vertex} (h : BoundaryCharts.Adj .corner u v) :
    -2 ≤ qCoord u ∧ rCoord u ≤ 1 := by
  cases u <;> cases v <;>
    simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, qCoord, rCoord] <;> omega

@[irreducible] def boundaryRootTrails (n : ℕ) : Finset (List Vertex) :=
  anchors.biUnion fun start =>
    (extensions (next .corner) n [start]).filter
      (fun trail => Leaf .corner start ∧ endsAt (Leaf .corner) trail)

theorem mem_boundaryRootTrails_iff (n : ℕ) (trail : List Vertex) :
    trail ∈ boundaryRootTrails n ↔ ∃ start ∈ anchors,
      Extends (next .corner) n [start] trail ∧ Leaf .corner start ∧
        endsAt (Leaf .corner) trail := by
  simp [boundaryRootTrails, mem_extensions_iff]

/-- Every boundary root of length at most six has an exact representative. -/
theorem boundary_root_representative {n : ℕ} (hn : n ≤ 6) {anchor : Vertex}
    {trail : List Vertex} (he : Extends (next .corner) n [anchor] trail)
    (hs : Leaf .corner anchor) (ht : endsAt (Leaf .corner) trail) :
    trail.map (normalize anchor) ∈ boundaryRootTrails n := by
  obtain ⟨hstep, hstart, hend⟩ := normalize_boundary_root hn he hs ht
  obtain ⟨hq, hr⟩ := leaf_anchor_bounds hs
  apply (mem_boundaryRootTrails_iff n (trail.map (normalize anchor))).mpr
  exact ⟨normalize anchor anchor, normalize_anchor_mem hq hr, hstep, hstart, hend⟩

@[irreducible] def boundaryRootEdges (n : ℕ) : Finset (Finset Edge) :=
  (boundaryRootTrails n).image traversalEdges

theorem traversalEdges_map (f : Vertex → Vertex) (trail : List Vertex) :
    traversalEdges (trail.map f) = (traversalEdges trail).image (Sym2.map f) := by
  induction trail with
  | nil => rfl
  | cons u rest ih =>
    cases rest with
    | nil => rfl
    | cons v rest =>
      simpa only [List.map_cons, traversalEdges, Finset.image_insert, Sym2.map_mk] using
        (congrArg (insert s(f u, f v)) ih)

theorem boundary_edges_representative {n : ℕ} (hn : n ≤ 6) {anchor : Vertex}
    {trail : List Vertex} (he : Extends (next .corner) n [anchor] trail)
    (hs : Leaf .corner anchor) (ht : endsAt (Leaf .corner) trail) :
    (traversalEdges trail).image (Sym2.map (normalize anchor)) ∈ boundaryRootEdges n := by
  rw [← traversalEdges_map]
  unfold boundaryRootEdges
  apply Finset.mem_image.mpr
  exact ⟨trail.map (normalize anchor), boundary_root_representative hn he hs ht, rfl⟩

/-- Six-cycle representatives retain all five nonclosing steps and the closing edge. -/
@[irreducible] def loopRootTrails : Finset (Vertex × List Vertex) :=
  anchors.biUnion fun start =>
    ((extensions (next .corner) 5 [start]).filter
      (endsAt (fun finish => BoundaryCharts.Adj .corner finish start))).image
        (fun trail => (start, trail))

theorem mem_loopRootTrails_iff (start : Vertex) (trail : List Vertex) :
    (start, trail) ∈ loopRootTrails ↔ start ∈ anchors ∧
      Extends (next .corner) 5 [start] trail ∧
        endsAt (fun finish => BoundaryCharts.Adj .corner finish start) trail := by
  simp [loopRootTrails, mem_extensions_iff]

/-- Every actual simple six-cycle is present after the same local normalization. -/
theorem loop_root_representative {anchor : Vertex} {trail : List Vertex}
    (he : Extends (next .corner) 5 [anchor] trail)
    (hc : endsAt (fun finish => BoundaryCharts.Adj .corner finish anchor) trail) :
    (normalize anchor anchor, trail.map (normalize anchor)) ∈ loopRootTrails := by
  have hp := extends_in_patch (by decide : 5 ≤ 27) he
  have hstep := normalize_extends he hp
  cases trail with
  | nil => exact False.elim hc
  | cons finish rest =>
    have hadj : BoundaryCharts.Adj .corner finish anchor := hc
    obtain ⟨hq, hr⟩ := adjacent_anchor_bounds (adj_symm hadj)
    apply (mem_loopRootTrails_iff (normalize anchor anchor)
      ((finish :: rest).map (normalize anchor))).mpr
    refine ⟨normalize_anchor_mem hq hr, by simpa using hstep, ?_⟩
    exact (normalize_adj_iff (hp finish (by simp)) (anchor_in_patch anchor)).mpr hadj

def closedEdges (p : Vertex × List Vertex) : Finset Edge :=
  match p.2 with
  | [] => ∅
  | finish :: rest => insert s(finish, p.1) (traversalEdges (finish :: rest))

@[irreducible] def loopRootEdges : Finset (Finset Edge) := loopRootTrails.image closedEdges

theorem closedEdges_map (f : Vertex → Vertex) (start : Vertex) (trail : List Vertex) :
    closedEdges (f start, trail.map f) = (closedEdges (start, trail)).image (Sym2.map f) := by
  cases trail with
  | nil => rfl
  | cons finish rest =>
    simp only [closedEdges, List.map_cons, Finset.image_insert, Sym2.map_mk]
    exact congrArg (insert s(f finish, f start)) (traversalEdges_map f (finish :: rest))

theorem loop_edges_representative {anchor : Vertex} {trail : List Vertex}
    (he : Extends (next .corner) 5 [anchor] trail)
    (hc : endsAt (fun finish => BoundaryCharts.Adj .corner finish anchor) trail) :
    (closedEdges (anchor, trail)).image (Sym2.map (normalize anchor)) ∈ loopRootEdges := by
  rw [← closedEdges_map]
  unfold loopRootEdges
  apply Finset.mem_image.mpr
  exact ⟨(normalize anchor anchor, trail.map (normalize anchor)),
    loop_root_representative he hc, rfl⟩

end RootedKP.ShortRootRepresentatives
