import RootedKP.Honeycomb
import Mathlib.Data.Sym.Sym2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity

/-!
# The actual AKLT polymer objects

A polymer is an unoriented finite edge set, together with its kind. Existence
of a simple traversal is a proposition, not extra counted data: reversing a
path or choosing a different first vertex of a loop gives the same polymer.
This distinction is essential in the counting certificate.
-/

namespace RootedKP.AKLT

open Honeycomb
open scoped BigOperators NNReal

abbrev Edge := Sym2 Vertex

def traversalEdges : List Vertex → Finset Edge
  | [] => ∅
  | [_] => ∅
  | u :: v :: rest => insert s(u, v) (traversalEdges (v :: rest))

def pathEdges {F : Rectangle} {s : ℕ} (p : BoundaryPath F s) : Finset Edge :=
  traversalEdges p.vertices

def loopEdges {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) : Finset Edge :=
  insert s(p.finish, p.start) (traversalEdges p.vertices)

theorem traversalEdges_nonempty {vs : List Vertex} (hl : 2 ≤ vs.length) :
    (traversalEdges vs).Nonempty := by
  cases vs with
  | nil => simp at hl
  | cons u rest =>
      cases rest with
      | nil => simp at hl
      | cons v rest => exact Finset.insert_nonempty ..

theorem pathEdges_nonempty {F : Rectangle} {s : ℕ} (p : BoundaryPath F s) :
    (pathEdges p).Nonempty := by
  apply traversalEdges_nonempty
  have hh := p.head_eq
  have ht := p.last_eq
  have hd := p.distinct
  cases hv : p.vertices with
  | nil => simp [hv] at hh
  | cons u rest =>
      cases rest with
      | nil => simp [hv] at hh ht; exact False.elim (hd (hh.symm.trans ht))
      | cons v rest => simp

theorem loopEdges_nonempty {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    (loopEdges p).Nonempty := Finset.insert_nonempty ..

inductive Kind where
  | path
  | loop
  deriving DecidableEq, Repr

/-- The fixed halo radius specified in the paper. -/
def haloRadius : ℕ := 200

def Realizes (F : Rectangle) (kind : Kind) (edges : Finset Edge) : Prop :=
  match kind with
  | .path => ∃ p : BoundaryPath F haloRadius, pathEdges p = edges
  | .loop => ∃ p : SimpleLoop F haloRadius, loopEdges p = edges

structure Polymer (F : Rectangle) where
  kind : Kind
  edges : Finset Edge
  realization : Realizes F kind edges

namespace Polymer

variable {F : Rectangle}

def length (p : Polymer F) : ℕ := p.edges.card

def support (p : Polymer F) : Finset Vertex := p.edges.biUnion Sym2.toFinset

def Incompatible (p q : Polymer F) : Prop := ¬ Disjoint p.support q.support

theorem edges_nonempty (p : Polymer F) : p.edges.Nonempty := by
  rcases p with ⟨kind, edges, h⟩
  cases kind with
  | path => obtain ⟨walk, rfl⟩ := h; exact pathEdges_nonempty walk
  | loop => obtain ⟨walk, rfl⟩ := h; exact loopEdges_nonempty walk

theorem support_nonempty (p : Polymer F) : p.support.Nonempty := by
  obtain ⟨e, he⟩ := p.edges_nonempty
  refine ⟨e.out.1, Finset.mem_biUnion.mpr ⟨e, he, ?_⟩⟩
  exact Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)

theorem incompatible_self (p : Polymer F) : Incompatible p p := by
  intro hd
  obtain ⟨v, hv⟩ := p.support_nonempty
  exact Finset.disjoint_left.mp hd hv hv

theorem length_pos (p : Polymer F) : 0 < p.length :=
  Finset.card_pos.mpr p.edges_nonempty

theorem incompatible_symm (p q : Polymer F) :
    Incompatible p q ↔ Incompatible q p := by
  simp only [Incompatible, disjoint_comm]

/-- `3 / 3^n` is exactly `3^(1-n)` for the nonempty polymers of the paper. -/
noncomputable def baseWeight (p : Polymer F) : ℝ :=
  (if p.kind = .path then (5 / 6 : ℝ) else 1) * (3 / (3 : ℝ) ^ p.length)

theorem baseWeight_nonneg (p : Polymer F) : 0 ≤ p.baseWeight := by
  unfold baseWeight
  split_ifs <;> positivity

/-- The exponentially tilted positive activity with mu=1/500. -/
noncomputable def activity (p : Polymer F) : ℝ≥0 :=
  ⟨p.baseWeight * Real.exp ((p.length : ℝ) / 500),
    mul_nonneg p.baseWeight_nonneg (Real.exp_pos _).le⟩

noncomputable def cost (p : Polymer F) : ℝ :=
  match p.length with
  | 3 => 52 / 100
  | 4 => 56 / 100
  | 5 => 66 / 100
  | 6 => 70 / 100
  | n => (17 / 100) * n

theorem cost_nonneg (p : Polymer F) : 0 ≤ p.cost := by
  unfold cost
  split <;> positivity

end Polymer
end RootedKP.AKLT
