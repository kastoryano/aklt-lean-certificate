import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# Exhaustive finite search for simple paths

This module proves completeness of a generic bounded-depth search, as well as
absence of repeated vertices and exact lengths of every generated traversal.
Vertices in a trail are stored in reverse traversal order. `Finset` removes
duplicate traversals but does not identify reversal or cyclic rotation.

This is the algorithmic foundation of a counting certificate, not a proof of
the numerical AKLT tables. The actual finite charts, orientation conventions,
table computations, and all-size chart transfer must still be supplied.
-/

namespace RootedKP.Enumeration

variable {V : Type*} [DecidableEq V]

/-- All extensions by `n` new vertices, avoiding every vertex already visited. -/
def extensions (next : V → Finset V) : ℕ → List V → Finset (List V)
  | 0, trail => {trail}
  | _ + 1, [] => ∅
  | n + 1, u :: us =>
      ((next u).filter (fun v => v ∉ u :: us)).biUnion
        (fun v => extensions next n (v :: u :: us))

/-- Independent relational specification of an extension by simple steps. -/
inductive Extends (next : V → Finset V) : ℕ → List V → List V → Prop
  | refl (trail) : Extends next 0 trail trail
  | step {u v us result n} : v ∈ next u → v ∉ u :: us →
      Extends next n (v :: u :: us) result →
      Extends next (n + 1) (u :: us) result

/-- The search returns exactly the traversals in its relational specification. -/
theorem mem_extensions_iff (next : V → Finset V) (n : ℕ) (trail result : List V) :
    result ∈ extensions next n trail ↔ Extends next n trail result := by
  induction n generalizing trail result with
  | zero =>
      simp only [extensions, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact .refl _
      · intro h
        cases h
        rfl
  | succ n ih =>
      cases trail with
      | nil =>
          simp only [extensions, Finset.notMem_empty, false_iff]
          intro h
          cases h
      | cons u us =>
          simp only [extensions, Finset.mem_biUnion, Finset.mem_filter]
          constructor
          · rintro ⟨v, ⟨hv, hnew⟩, hrest⟩
            exact .step hv hnew ((ih _ _).mp hrest)
          · intro h
            cases h with
            | step hv hnew hrest => exact ⟨_, ⟨hv, hnew⟩, (ih _ _).mpr hrest⟩

omit [DecidableEq V] in
theorem Extends.length {next : V → Finset V} {n : ℕ} {trail result : List V}
    (h : Extends next n trail result) : result.length = trail.length + n := by
  induction h with
  | refl trail => simp
  | step _ _ _ ih => simp_all; omega

omit [DecidableEq V] in
theorem Extends.nodup {next : V → Finset V} {n : ℕ} {trail result : List V}
    (h : Extends next n trail result) (hp : trail.Nodup) : result.Nodup := by
  induction h with
  | refl trail => exact hp
  | step _ hnew _ ih => exact ih (List.nodup_cons.mpr ⟨hnew, hp⟩)

/-- A concrete bounded search can therefore be used to certify simple-path counts. -/
theorem generated_paths_simple (next : V → Finset V) (n : ℕ) (start : V)
    {result : List V} (h : result ∈ extensions next n [start]) :
    result.Nodup ∧ result.length = n + 1 := by
  have he := (mem_extensions_iff next n [start] result).mp h
  exact ⟨he.nodup (by simp), by simpa [Nat.add_comm] using he.length⟩

/-- In an undirected graph of degree at most three, after the first edge there
are at most two choices per additional simple step. This holds at every depth;
it is an analytic-tail counting bound, not a bounded enumeration experiment. -/
theorem card_extensions_after_edge_le (next : V → Finset V)
    (hsymm : ∀ u v, v ∈ next u → u ∈ next v)
    (hdegree : ∀ u, (next u).card ≤ 3) (n : ℕ) :
    ∀ u v rest, v ∈ next u → (extensions next n (u :: v :: rest)).card ≤ 2 ^ n := by
  induction n with
  | zero => intro u v rest huv; simp [extensions]
  | succ n ih =>
      intro u v rest huv
      let choices := (next u).filter (fun w => w ∉ u :: v :: rest)
      have hchoices : choices.card ≤ 2 := by
        have hsub : choices ⊆ (next u).erase v := by
          intro w hw
          obtain ⟨hw, hnew⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_erase.mpr ⟨by intro h; subst w; simp at hnew, hw⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem huv] at hc
        have hd := hdegree u
        omega
      calc
        (extensions next (n + 1) (u :: v :: rest)).card ≤
            ∑ w ∈ choices, (extensions next n (w :: u :: v :: rest)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ choices, 2 ^ n := by
          apply Finset.sum_le_sum
          intro w hw
          exact ih w u (v :: rest) (hsymm u w (Finset.mem_filter.mp hw).1)
        _ = choices.card * 2 ^ n := by simp
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ hchoices
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

end RootedKP.Enumeration
