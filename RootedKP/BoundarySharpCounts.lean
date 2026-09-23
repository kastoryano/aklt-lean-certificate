import RootedKP.BoundaryPrunedCounts

namespace RootedKP.BoundaryCounts
open Honeycomb BoundaryCharts Enumeration LoopCounts
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Besides lying at heightQ=-3, a left-ray leaf has heightS≤-3. -/
def cornerPossible (n : ℕ) (u : Vertex) : Prop :=
  reachesHeight heightQ (-3) n u ∧ heightS u + 3 ≤ (n : ℤ)
instance (n : ℕ) (u : Vertex) : Decidable (cornerPossible n u) := by
  unfold cornerPossible
  infer_instance

theorem cornerPossible_necessary (n : ℕ) (u : Vertex) (us result : List Vertex)
    (he : Extends (next .corner) n (u :: us) result) (ha : endsAt leftLeaf result) :
    cornerPossible n u := by
  constructor
  · apply reachesHeight_necessary .corner heightQ heightQ_lipschitz (-3) leftLeaf ?_ n u us result he ha
    intro v hv
    cases v <;> simp_all [leftLeaf, heightQ]
  · cases result with
    | nil => exact False.elim ha
    | cons v vs =>
      change leftLeaf v at ha
      have hs := extension_height_bounds .corner heightS heightS_lipschitz he u us v vs rfl rfl
      have hv : heightS v ≤ -3 := by cases v <;> simp_all [leftLeaf, heightS] <;> omega
      omega

def cornerStartCount (n k : ℕ) : ℕ :=
  prunedCount .corner (endsAt leftLeaf) cornerPossible n [.a ((k : ℤ) - 1) 1]

theorem cornerStartCount_eq (n k : ℕ) :
    cornerStartCount n k = acceptedCount (next .corner) (endsAt leftLeaf) n [.a ((k : ℤ) - 1) 1] := by
  unfold cornerStartCount
  rw [prunedCount_eq _ _ _ cornerPossible_necessary, fastCount_eq]

theorem cornerCount_eq_sum_starts (n : ℕ) : cornerCount n = ∑ k ∈ Finset.range n, cornerStartCount n k := by
  unfold cornerCount
  simp_rw [cornerStartCount_eq]

/-- Positive side endpoints satisfy heightR≥2 and heightS≥4. -/
def sidePossible (n : ℕ) (u : Vertex) : Prop :=
  reachesHeight heightQ 2 n u ∧ 2 - heightR u ≤ (n : ℤ) ∧ 4 - heightS u ≤ (n : ℤ)
instance (n : ℕ) (u : Vertex) : Decidable (sidePossible n u) := by
  unfold sidePossible
  infer_instance

theorem sidePossible_necessary (n : ℕ) (u : Vertex) (us result : List Vertex)
    (he : Extends (next .side) n (u :: us) result) (ha : endsAt sideAbove result) :
    sidePossible n u := by
  refine ⟨?_, ?_⟩
  · apply reachesHeight_necessary .side heightQ heightQ_lipschitz 2 sideAbove ?_ n u us result he ha
    intro v hv
    cases v <;> simp_all [sideAbove, heightQ]
  · cases result with
    | nil => exact False.elim ha
    | cons v vs =>
      change sideAbove v at ha
      have hr := extension_height_bounds .side heightR heightR_lipschitz he u us v vs rfl rfl
      have hs := extension_height_bounds .side heightS heightS_lipschitz he u us v vs rfl rfl
      have hv : 2 ≤ heightR v ∧ 4 ≤ heightS v := by
        cases v <;> simp_all [sideAbove, heightR, heightS] <;> constructor <;> omega
      constructor <;> omega

def sharpSideCount (n : ℕ) : ℕ :=
  prunedCount .side (endsAt sideAbove) sidePossible n [.a 1 0]

theorem sharpSideCount_eq (n : ℕ) : sharpSideCount n = sideCount n := by
  unfold sharpSideCount sideCount
  rw [prunedCount_eq _ _ _ sidePossible_necessary, fastCount_eq]

end RootedKP.BoundaryCounts
