import RootedKP.BoundaryPrefixCertificates

/-!
# Certified endpoint-distance pruning

A pruning predicate is used only after proving it necessary for every accepted
extension. No traversal is removed on the basis of a numerical experiment.
-/
namespace RootedKP.BoundaryCounts
open Honeycomb BoundaryCharts Enumeration LoopCounts
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def prunedCount (C : Chart) (accept : List Vertex → Prop) [DecidablePred accept]
    (possible : ℕ → Vertex → Prop) [∀ n, DecidablePred (possible n)] :
    ℕ → List Vertex → ℕ
  | 0, trail => if accept trail then 1 else 0
  | _ + 1, [] => 0
  | n + 1, u :: us =>
    if possible (n + 1) u then
      (neighborList u).foldr (fun v acc =>
        (if (core C u ∨ core C v) ∧ v ∉ u :: us then
          prunedCount C accept possible n (v :: u :: us) else 0) + acc) 0
    else 0

theorem prunedCount_eq (C : Chart) (accept : List Vertex → Prop) [DecidablePred accept]
    (possible : ℕ → Vertex → Prop) [∀ n, DecidablePred (possible n)]
    (hnecessary : ∀ n u us result, Extends (next C) n (u :: us) result →
      accept result → possible n u) (n : ℕ) (trail : List Vertex) :
    prunedCount C accept possible n trail = fastCount C accept n trail := by
  induction n generalizing trail with
  | zero => rfl
  | succ n ih =>
    cases trail with
    | nil => rfl
    | cons u us =>
      by_cases hp : possible (n + 1) u
      · simp only [prunedCount, if_pos hp, fastCount, ih]
      · simp only [prunedCount, if_neg hp]
        symm
        rw [fastCount_eq, acceptedCount_eq_card, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro result hr
        obtain ⟨he, ha⟩ := Finset.mem_filter.mp hr
        exact hp (hnecessary _ _ _ _ ((mem_extensions_iff _ _ _ _).mp he) ha)

/-- Necessary distance to one specified endpoint height. -/
def reachesHeight (height : Vertex → ℤ) (target : ℤ) (n : ℕ) (u : Vertex) : Prop :=
  height u - target ≤ (n : ℤ) ∧ target - height u ≤ (n : ℤ)

instance (height : Vertex → ℤ) (target : ℤ) (n : ℕ) (u : Vertex) :
    Decidable (reachesHeight height target n u) := by
  unfold reachesHeight
  infer_instance

theorem reachesHeight_necessary (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) (target : ℤ) (accept : Vertex → Prop)
    (htarget : ∀ v, accept v → height v = target)
    (n : ℕ) (u : Vertex) (us result : List Vertex)
    (he : Extends (next C) n (u :: us) result) (ha : endsAt accept result) :
    reachesHeight height target n u := by
  cases result with
  | nil => exact False.elim ha
  | cons v vs =>
    have hb := extension_height_bounds C height lip he u us v vs rfl rfl
    have hv := htarget v ha
    unfold reachesHeight
    rw [hv] at hb
    exact hb.symm

def endpointPossible (C : Chart) (n : ℕ) (u : Vertex) : Prop :=
  match C with
  | .bulk => False
  | .side => reachesHeight heightQ 2 n u
  | .corner => reachesHeight heightQ (-3) n u ∨ reachesHeight heightR 2 n u

instance (C : Chart) (n : ℕ) (u : Vertex) : Decidable (endpointPossible C n u) := by
  cases C <;> unfold endpointPossible <;> infer_instance

theorem endpointPossible_necessary (C : Chart) (n : ℕ) (u : Vertex) (us result : List Vertex)
    (he : Extends (next C) n (u :: us) result) (ha : endsAt (leafCode C) result) :
    endpointPossible C n u := by
  cases C with
  | bulk => cases result <;> exact False.elim ha
  | side =>
    apply reachesHeight_necessary .side heightQ heightQ_lipschitz 2 (leafCode .side) ?_ n u us result he ha
    intro v hv
    cases v <;> simp_all [leafCode, heightQ]
  | corner =>
    cases result with
    | nil => exact False.elim ha
    | cons v vs =>
      change upperLeaf v ∨ leftLeaf v at ha
      rcases ha with hu | hl
      · apply Or.inr
        apply reachesHeight_necessary .corner heightR heightR_lipschitz 2 upperLeaf ?_ n u us (v :: vs) he hu
        intro w hw
        cases w <;> simp_all [upperLeaf, heightR]
      · apply Or.inl
        apply reachesHeight_necessary .corner heightQ heightQ_lipschitz (-3) leftLeaf ?_ n u us (v :: vs) he hl
        intro w hw
        cases w <;> simp_all [leftLeaf, heightQ]

def prunedEndpointCount (C : Chart) : ℕ → Vertex → Vertex → ℕ
  | 0, u, _ => if leafCode C u then 1 else 0
  | n + 1, u, forbidden =>
    (neighborList u).foldr (fun v acc =>
      (if (core C u ∨ core C v) ∧ v ≠ forbidden then
        prunedCount C (endsAt (leafCode C)) (endpointPossible C) n [v, u] else 0) + acc) 0

theorem prunedEndpointCount_eq (C : Chart) (n : ℕ) (u forbidden : Vertex) :
    prunedEndpointCount C n u forbidden = endpointFastCount C n u forbidden := by
  cases n <;> simp only [prunedEndpointCount, endpointFastCount,
    prunedCount_eq C _ _ (endpointPossible_necessary C)]

def prunedCornerCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, prunedCount .corner (endsAt leftLeaf)
    (reachesHeight heightQ (-3)) n [.a ((k : ℤ) - 1) 1]

theorem prunedCornerCount_eq (n : ℕ) : prunedCornerCount n = cornerCount n := by
  rw [← fastCornerCount_eq]
  apply Finset.sum_congr rfl
  intro k _
  apply prunedCount_eq
  apply reachesHeight_necessary .corner heightQ heightQ_lipschitz (-3) leftLeaf
  intro v hv
  cases v <;> simp_all [leftLeaf, heightQ]

def prunedSideCount (n : ℕ) : ℕ :=
  prunedCount .side (endsAt sideAbove) (reachesHeight heightQ 2) n [.a 1 0]

theorem prunedSideCount_eq (n : ℕ) : prunedSideCount n = sideCount n := by
  unfold prunedSideCount sideCount
  rw [← fastCount_eq]
  apply prunedCount_eq
  apply reachesHeight_necessary .side heightQ heightQ_lipschitz 2 sideAbove
  intro v hv
  cases v <;> simp_all [sideAbove, heightQ]

end RootedKP.BoundaryCounts
