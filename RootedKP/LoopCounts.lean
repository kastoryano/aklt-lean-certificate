import RootedKP.Enumeration
import RootedKP.Honeycomb

/-!
# Exact anchored honeycomb loop enumeration

We fix the directed edge a(0,0) → b(0,0). A simple cycle containing this
edge has one traversal starting with this orientation. Trails are stored in
reverse order, following the generic, proved-complete enumerator.

The cardinality statements below are kernel reductions of this enumerator,
not imported numerical assertions or native computation certificates.
Only the explicitly listed lengths have been checked here. In particular,
this file does not assert the complete table through length 28 or its sun-chart
coverage.
-/

namespace RootedKP.LoopCounts

open Honeycomb Enumeration

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

section AcceptedCounts

variable {V : Type*} [DecidableEq V]

theorem extends_drop {next : V → Finset V} {n : ℕ} {trail result : List V}
    (h : Extends next n trail result) : result.drop n = trail := by
  induction h with
  | refl trail => simp
  | step _ _ _ ih =>
      rw [← List.drop_drop, ih]
      rfl

/-- Direct counts avoid constructing the (much larger) set of all traversals. -/
def acceptedCount (next : V → Finset V) (accept : List V → Prop)
    [DecidablePred accept] : ℕ → List V → ℕ
  | 0, trail => if accept trail then 1 else 0
  | _ + 1, [] => 0
  | n + 1, u :: us =>
      ∑ v ∈ (next u).filter (fun v => v ∉ u :: us),
        acceptedCount next accept n (v :: u :: us)

/-- Soundness and completeness of the faster counting implementation. -/
theorem acceptedCount_eq_card (next : V → Finset V) (accept : List V → Prop)
    [DecidablePred accept] (n : ℕ) (trail : List V) :
    acceptedCount next accept n trail = ((extensions next n trail).filter accept).card := by
  induction n generalizing trail with
  | zero =>
      by_cases h : accept trail
      · have hf : Finset.filter accept {trail} = {trail} := by
          ext x
          simp
          rintro rfl
          exact h
        simp [acceptedCount, extensions, h, hf]
      · have hf : Finset.filter accept {trail} = ∅ := by
          ext x
          simp
          rintro rfl
          exact h
        simp [acceptedCount, extensions, h, hf]
  | succ n ih =>
      cases trail with
      | nil => simp [acceptedCount, extensions]
      | cons u us =>
          rw [extensions, Finset.filter_biUnion, Finset.card_biUnion]
          · simp only [acceptedCount]
            exact Finset.sum_congr rfl (fun v _ => ih (v :: u :: us))
          · intro v hv w hw hne
            apply Finset.disjoint_left.mpr
            intro result hr₁ hr₂
            have he₁ := (mem_extensions_iff next n (v :: u :: us) result).mp
              (Finset.mem_filter.mp hr₁).1
            have he₂ := (mem_extensions_iff next n (w :: u :: us) result).mp
              (Finset.mem_filter.mp hr₂).1
            have heq : v :: u :: us = w :: u :: us :=
              (extends_drop he₁).symm.trans (extends_drop he₂)
            exact hne (List.cons.inj heq).1

end AcceptedCounts

def origin : Vertex := .a 0 0
def first : Vertex := .b 0 0

def closes : List Vertex → Prop
  | [] => False
  | u :: _ => Adj u origin

instance (trail : List Vertex) : Decidable (closes trail) := by
  cases trail <;> unfold closes <;> infer_instance

def withinClosingDistance (n : ℕ) (u : Vertex) : Prop :=
  -(n + 1 : ℤ) ≤ heightQ u ∧ heightQ u ≤ (n + 1 : ℤ) ∧
  -(n + 1 : ℤ) ≤ heightR u ∧ heightR u ≤ (n + 1 : ℤ) ∧
  -(n + 1 : ℤ) ≤ heightS u ∧ heightS u ≤ (n + 1 : ℤ)

instance (n : ℕ) (u : Vertex) : Decidable (withinClosingDistance n u) := by
  unfold withinClosingDistance
  infer_instance

theorem extension_closing_height_bounds (height : Vertex → ℤ)
    (lip : OneLipschitz height) (hzero : height origin = 0)
    {n : ℕ} {trail result : List Vertex}
    (he : Extends neighbors n trail result) (hc : closes result) :
    match trail with
    | [] => False
    | u :: _ => height u ≤ (n + 1 : ℤ) ∧ -height u ≤ (n + 1 : ℤ) := by
  induction he with
  | refl trail =>
      cases trail with
      | nil => exact hc
      | cons u us =>
          have hb := lip u origin hc
          simp only [hzero] at hb
          dsimp
          omega
  | @step u v us result n hv _ _ ih =>
      have hb := lip u v ((mem_neighbors u v).mp hv)
      have hi := ih hc
      dsimp at hi ⊢
      constructor <;> omega

theorem extension_closing_within {n : ℕ} {u : Vertex} {us result : List Vertex}
    (he : Extends neighbors n (u :: us) result) (hc : closes result) :
    withinClosingDistance n u := by
  have hq := extension_closing_height_bounds heightQ heightQ_lipschitz
    (by rfl : heightQ origin = 0) he hc
  have hr := extension_closing_height_bounds heightR heightR_lipschitz
    (by rfl : heightR origin = 0) he hc
  have hs := extension_closing_height_bounds heightS heightS_lipschitz
    (by rfl : heightS origin = 0) he hc
  dsimp at hq hr hs
  unfold withinClosingDistance
  omega

theorem count_zero_outside {n : ℕ} {u : Vertex} {us : List Vertex}
    (h : ¬ withinClosingDistance n u) : acceptedCount neighbors closes n (u :: us) = 0 := by
  rw [acceptedCount_eq_card, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro result hresult
  have hm := Finset.mem_filter.mp hresult
  exact h (extension_closing_within ((mem_extensions_iff _ _ _ _).mp hm.1) hm.2)

/-- Verified closing-distance pruning, using the three graph-Lipschitz heights. -/
def prunedCount : ℕ → List Vertex → ℕ
  | 0, trail => if closes trail then 1 else 0
  | _ + 1, [] => 0
  | n + 1, u :: us =>
      if withinClosingDistance (n + 1) u then
        ∑ v ∈ (neighbors u).filter (fun v => v ∉ u :: us),
          prunedCount n (v :: u :: us)
      else 0

theorem prunedCount_eq (n : ℕ) (trail : List Vertex) :
    prunedCount n trail = acceptedCount neighbors closes n trail := by
  induction n generalizing trail with
  | zero => rfl
  | succ n ih =>
      cases trail with
      | nil => rfl
      | cons u us =>
          by_cases h : withinClosingDistance (n + 1) u
          · simp only [prunedCount, if_pos h, acceptedCount]
            exact Finset.sum_congr rfl (fun v _ => ih (v :: u :: us))
          · rw [prunedCount, if_neg h, count_zero_outside h]

/-- Exactly `n` distinct cycle vertices, with the closing edge implicit. -/
def anchoredLoops (n : ℕ) : Finset (List Vertex) :=
  (extensions neighbors (n - 2) [first, origin]).filter closes

theorem mem_anchoredLoops_iff (n : ℕ) (trail : List Vertex) :
    trail ∈ anchoredLoops n ↔
      Extends neighbors (n - 2) [first, origin] trail ∧ closes trail := by
  simp only [anchoredLoops, Finset.mem_filter, mem_extensions_iff]

theorem anchoredLoops_simple {n : ℕ} (hn : 2 ≤ n) {trail : List Vertex}
    (h : trail ∈ anchoredLoops n) : trail.Nodup ∧ trail.length = n := by
  have he := ((mem_anchoredLoops_iff n trail).mp h).1
  have hlen := he.length
  have hnodup := he.nodup (by simp [first, origin])
  refine ⟨hnodup, ?_⟩
  simp only [List.length_cons, List.length_nil] at hlen
  omega

theorem loops4 : (anchoredLoops 4).card = 0 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card]
  rw [← prunedCount_eq]
  decide +kernel
theorem loops6 : (anchoredLoops 6).card = 2 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card]
  rw [← prunedCount_eq]
  decide +kernel
theorem loops8 : (anchoredLoops 8).card = 0 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card]
  rw [← prunedCount_eq]
  decide +kernel
theorem loops10 : (anchoredLoops 10).card = 10 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card]
  rw [← prunedCount_eq]
  decide +kernel

end RootedKP.LoopCounts

#print axioms RootedKP.LoopCounts.loops10
#print axioms RootedKP.LoopCounts.anchoredLoops_simple
