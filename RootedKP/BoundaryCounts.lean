import RootedKP.BoundaryCharts
import RootedKP.LoopCounts
import RootedKP.Arithmetic

/-!
# Complete local-chart boundary-path searches

The corner search counts every simple traversal from the upper leaf ray to the
left leaf ray exactly once. Its finite start range is proved sufficient using
the graph-Lipschitz heightS, not assumed from an observed enumeration cutoff.
The side search fixes one leaf and counts paths to leaves above it.
-/

namespace RootedKP.BoundaryCounts

open Honeycomb BoundaryCharts Enumeration LoopCounts
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def endsAt (accept : Vertex → Prop) : List Vertex → Prop
  | [] => False
  | v :: _ => accept v

instance (accept : Vertex → Prop) [DecidablePred accept] (trail : List Vertex) :
    Decidable (endsAt accept trail) := by
  cases trail <;> unfold endsAt <;> infer_instance

def pathsTo (C : Chart) (accept : Vertex → Prop) [DecidablePred accept]
    (n : ℕ) (start : Vertex) : Finset (List Vertex) :=
  (extensions (next C) n [start]).filter (endsAt accept)

theorem mem_pathsTo_iff (C : Chart) (accept : Vertex → Prop) [DecidablePred accept]
    (n : ℕ) (start : Vertex) (trail : List Vertex) :
    trail ∈ pathsTo C accept n start ↔
      Extends (next C) n [start] trail ∧ endsAt accept trail := by
  simp only [pathsTo, Finset.mem_filter, mem_extensions_iff]

theorem pathsTo_simple {C : Chart} {accept : Vertex → Prop} [DecidablePred accept]
    {n : ℕ} {start : Vertex} {trail : List Vertex}
    (h : trail ∈ pathsTo C accept n start) : trail.Nodup ∧ trail.length = n + 1 :=
  generated_paths_simple (next C) n start (Finset.mem_filter.mp h).1

def cornerPaths (n : ℕ) : Finset (List Vertex) :=
  (Finset.range n).biUnion (fun k => pathsTo .corner leftLeaf n (.a ((k : ℤ) - 1) 1))

/-- Independent specification: any start on the infinite upper leaf ray. -/
def CornerTraversal (n : ℕ) (trail : List Vertex) : Prop :=
  ∃ q : ℤ, -1 ≤ q ∧ Extends (next .corner) n [.a q 1] trail ∧ endsAt leftLeaf trail

/-- Every path crossing the corner starts in the enumerated finite range. -/
theorem corner_start_bound {n : ℕ} {q : ℤ} {trail : List Vertex}
    (hq : -1 ≤ q) (he : Extends (next .corner) n [.a q 1] trail)
    (hend : endsAt leftLeaf trail) : q + 1 < (n : ℤ) := by
  cases trail with
  | nil => exact False.elim hend
  | cons v vs =>
    cases v with
    | a q' r => exact False.elim hend
    | b q' r =>
      obtain ⟨rfl, hr⟩ := hend
      have hb := extension_height_bounds .corner heightS heightS_lipschitz he
        (.a q 1) [] (.b (-2) r) vs rfl rfl
      simp only [heightS] at hb
      omega

/-- Soundness and completeness for the full infinite corner chart. -/
theorem mem_cornerPaths_iff (n : ℕ) (trail : List Vertex) :
    trail ∈ cornerPaths n ↔ CornerTraversal n trail := by
  simp only [cornerPaths, Finset.mem_biUnion, Finset.mem_range, mem_pathsTo_iff]
  constructor
  · rintro ⟨k, hk, he, hend⟩
    exact ⟨(k : ℤ) - 1, by omega, he, hend⟩
  · rintro ⟨q, hq, he, hend⟩
    have hb := corner_start_bound hq he hend
    let k := (q + 1).toNat
    have hk : (k : ℤ) = q + 1 := Int.toNat_of_nonneg (by omega)
    refine ⟨k, by omega, ?_, hend⟩
    have heq : (k : ℤ) - 1 = q := by omega
    simpa only [heq] using he

/-- Counting implementation equivalent to the complete set of corner traversals. -/
def cornerCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n,
    acceptedCount (next .corner) (endsAt leftLeaf) n [.a ((k : ℤ) - 1) 1]

theorem cornerCount_eq_card (n : ℕ) : cornerCount n = (cornerPaths n).card := by
  unfold cornerPaths cornerCount
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    exact acceptedCount_eq_card _ _ _ _
  · intro k hk l hl hne
    apply Finset.disjoint_left.mpr
    intro trail hk' hl'
    have he₁ := ((mem_pathsTo_iff _ _ _ _ _).mp hk').1
    have he₂ := ((mem_pathsTo_iff _ _ _ _ _).mp hl').1
    have heq := (extends_drop he₁).symm.trans (extends_drop he₂)
    have : k = l := by simpa using heq
    exact hne this

/-- Positive boundary direction on the straight side q≤0. -/
def sideAbove : Vertex → Prop
  | .a q r => q = 1 ∧ 0 < r
  | _ => False

instance (v : Vertex) : Decidable (sideAbove v) := by
  cases v <;> unfold sideAbove <;> infer_instance

def sidePaths (n : ℕ) := pathsTo .side sideAbove n (.a 1 0)
def sideCount (n : ℕ) : ℕ := acceptedCount (next .side) (endsAt sideAbove) n [.a 1 0]

theorem sideCount_eq_card (n : ℕ) : sideCount n = (sidePaths n).card :=
  acceptedCount_eq_card _ _ _ _

theorem mem_sidePaths_iff (n : ℕ) (trail : List Vertex) :
    trail ∈ sidePaths n ↔
      Extends (next .side) n [.a 1 0] trail ∧ endsAt sideAbove trail :=
  mem_pathsTo_iff _ _ _ _ _

/-- These are computations of the proved-complete search, not checks of
independently supplied numerals. -/
theorem cornerCount_three : cornerCount 3 = 1 := by decide +kernel
theorem cornerCount_five : cornerCount 5 = 2 := by decide +kernel
theorem cornerCount_seven : cornerCount 7 = 7 := by decide +kernel

theorem sideCount_four : sideCount 4 = 1 := by decide +kernel
theorem sideCount_six : sideCount 6 = 1 := by decide +kernel
theorem sideCount_eight : sideCount 8 = 4 := by decide +kernel

/-- Prefix agreement with the arithmetic input data. This does not certify the
remaining table entries or the all-size transfer into these local charts. -/
theorem corner_prefix_matches_arithmetic :
    [cornerCount 3, cornerCount 5, cornerCount 7] = Arithmetic.oddCounts.take 3 := by
  rw [cornerCount_three, cornerCount_five, cornerCount_seven]
  rfl

theorem side_eight_matches_arithmetic : sideCount 8 = Arithmetic.evenCountsFrom8[0]! := by
  rw [sideCount_eight]
  rfl

end RootedKP.BoundaryCounts
