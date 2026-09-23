import RootedKP.Honeycomb
import RootedKP.Enumeration

/-!
# Exact local sun charts

These graphs are infinite, so bounded-depth searches impose no coordinate-box
cutoff. They are the bulk, straight-side and convex-corner face patterns used
by the radius-100 C++ search. Transfer from an arbitrary halo to these charts
is a separate geometric theorem, not assumed here.
-/

namespace RootedKP.BoundaryCharts

open Honeycomb

inductive Chart where
  | bulk | side | corner
  deriving DecidableEq, Repr

def FaceIn : Chart → Face → Prop
  | .bulk, _ => True
  | .side, f => f.1 ≤ 0
  | .corner, f => 0 ≤ f.1 ∧ f.2 ≤ 0

instance (C : Chart) (f : Face) : Decidable (FaceIn C f) := by
  cases C <;> unfold FaceIn <;> infer_instance

/-- A chart vertex is core precisely when one of its incident faces is retained. -/
def Core (C : Chart) (v : Vertex) : Prop := ∃ f, FaceIn C f ∧ Incident v f

/-- Computable form of the incident-face predicate, including both vertex phases. -/
def core (C : Chart) : Vertex → Prop
  | .a q r | .b q r =>
    match C with
    | .bulk => True
    | .side => q ≤ 0
    | .corner => -1 ≤ q ∧ r ≤ 0

instance (C : Chart) (v : Vertex) : Decidable (core C v) := by
  cases v <;> cases C <;> unfold core <;> infer_instance

theorem core_iff (C : Chart) (v : Vertex) : core C v ↔ Core C v := by
  cases v <;> cases C <;>
    simp [core, Core, Incident, FaceIn, and_or_left, exists_or] <;> omega

def Adj (C : Chart) (u v : Vertex) : Prop :=
  Honeycomb.Adj u v ∧ (core C u ∨ core C v)

instance (C : Chart) (u v : Vertex) : Decidable (Adj C u v) := by
  unfold Adj
  infer_instance

def next (C : Chart) (u : Vertex) : Finset Vertex :=
  (neighbors u).filter (fun v => core C u ∨ core C v)

@[simp] theorem mem_next (C : Chart) (u v : Vertex) : v ∈ next C u ↔ Adj C u v := by
  simp [next, Adj]

theorem adj_symm {C : Chart} {u v : Vertex} (h : Adj C u v) : Adj C v u :=
  ⟨Honeycomb.adj_symm h.1, h.2.symm⟩

def Leaf (C : Chart) (u : Vertex) : Prop := (next C u).card = 1

instance (C : Chart) (u : Vertex) : Decidable (Leaf C u) := by
  unfold Leaf
  infer_instance

/-- Coordinates of the two corner leaf rays, with their actual phases. -/
def upperLeaf : Vertex → Prop
  | .a q r => -1 ≤ q ∧ r = 1
  | _ => False

def leftLeaf : Vertex → Prop
  | .b q r => q = -2 ∧ r ≤ 0
  | _ => False

instance (v : Vertex) : Decidable (upperLeaf v) := by
  cases v <;> unfold upperLeaf <;> infer_instance
instance (v : Vertex) : Decidable (leftLeaf v) := by
  cases v <;> unfold leftLeaf <;> infer_instance

theorem upperLeaf_is_leaf {v : Vertex} (hv : upperLeaf v) : Leaf .corner v := by
  cases v with
  | a q r =>
    obtain ⟨hq, rfl⟩ := hv
    have hn : next .corner (.a q 1) = {.b q 0} := by
      ext v
      cases v <;> simp [Adj, Honeycomb.Adj, core] <;> omega
    rw [Leaf, hn]
    simp
  | b q r => exact False.elim hv

theorem leftLeaf_is_leaf {v : Vertex} (hv : leftLeaf v) : Leaf .corner v := by
  cases v with
  | a q r => exact False.elim hv
  | b q r =>
    obtain ⟨rfl, hr⟩ := hv
    have hn : next .corner (.b (-2) r) = {.a (-1) r} := by
      ext v
      cases v <;> simp [Adj, Honeycomb.Adj, core] <;> omega
    rw [Leaf, hn]
    simp

/-- Every generated step is a genuine ambient honeycomb edge. -/
theorem extension_height_bounds (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) {n : ℕ} {trail result : List Vertex}
    (he : Enumeration.Extends (next C) n trail result) :
    ∀ u us v vs, trail = u :: us → result = v :: vs →
      height v - height u ≤ (n : ℤ) ∧ height u - height v ≤ (n : ℤ) := by
  induction he with
  | refl trail =>
    intro u us v vs hu hv
    have : u = v := (List.cons.inj (hu.symm.trans hv)).1
    subst v
    simp
  | @step u v us result n hv _ _ ih =>
    intro x xs y ys hx hy
    have hxu : x = u := (List.cons.inj hx.symm).1
    subst x
    have hstep := lip u v ((mem_next C u v).mp hv).1
    have hrest := ih v (u :: us) y ys rfl hy
    constructor <;> omega

end RootedKP.BoundaryCharts
