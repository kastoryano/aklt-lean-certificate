import RootedKP.PathConfinement
import RootedKP.BoundaryCoordinates

namespace RootedKP.Honeycomb
namespace BoundaryLeaves

/-- The oriented leaf row assigned to one of the six face-polygon sides. -/
def leaf (F : Rectangle) (i : Fin 6) (r : ℤ) : Vertex :=
  fromChart i (.a ((sideChart F 200 i).Q + 1) r)

def attachment (F : Rectangle) (i : Fin 6) (r : ℤ) : Vertex :=
  fromChart i (.b (sideChart F 200 i).Q r)

def Valid (F : Rectangle) (i : Fin 6) (r : ℤ) : Prop :=
  (sideChart F 200 i).r₀ - 1 ≤ r ∧ r < (sideChart F 200 i).r₁

/-- The first leaf of each row is excluded from right-endpoint candidates. -/
def Candidate (F : Rectangle) (i : Fin 6) (r : ℤ) : Prop :=
  (sideChart F 200 i).r₀ ≤ r ∧ r < (sideChart F 200 i).r₁

theorem candidate_valid {F : Rectangle} {i : Fin 6} {r : ℤ}
    (h : Candidate F i r) : Valid F i r := by unfold Candidate Valid at *; omega

theorem attachment_eq_point (F : Rectangle) (i : Fin 6) (r : ℤ) :
    attachment F i r = BoundaryCycle.point F 0 i (2*r+1) := by
  simp only [attachment, BoundaryCycle.point, Nat.cast_zero, sub_zero, vertexAt_odd]

theorem parameter_valid {F : Rectangle} {i : Fin 6} {r : ℤ} (h : Valid F i r) :
    BoundaryCycle.lower F 0 i ≤ 2*r+1 ∧ 2*r+1 < BoundaryCycle.upper F i := by
  unfold Valid BoundaryCycle.lower BoundaryCycle.upper at *
  omega

theorem leaf_prong (F : Rectangle) (i : Fin 6) (r : ℤ) :
    Adj (leaf F i r) (attachment F i r) := by
  apply fromChart_adj
  simp [Adj]

theorem attachment_core {F : Rectangle} {i : Fin 6} {r : ℤ} (h : Valid F i r) :
    Core F 200 (attachment F i r) := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;>
    simp only [attachment, fromChart, sideChart, rotate, Valid,
      core_a_coordinates, core_b_coordinates] at h ⊢ <;> omega

theorem leaf_not_core {F : Rectangle} {i : Fin 6} {r : ℤ} :
    ¬ Core F 200 (leaf F i r) := by
  fin_cases i <;> simp only [leaf, fromChart, sideChart, rotate,
    core_a_coordinates, core_b_coordinates] <;> omega

theorem leaf_is_leaf {F : Rectangle} {i : Fin 6} {r : ℤ} (h : Valid F i r) :
    Leaf F 200 (leaf F i r) :=
  noncore_sun_vertex_is_leaf ⟨attachment F i r, leaf_prong F i r, Or.inr (attachment_core h)⟩
    leaf_not_core

/-- Exhaustive parametrization of the actual finite-region leaves. -/
theorem leaf_coverage {F : Rectangle} {v : Vertex} (hv : Leaf F 200 v) :
    ∃ i : Fin 6, ∃ r : ℤ, Valid F i r ∧ v = leaf F i r := by
  have hs := leaf_on_support_height hv
  obtain ⟨w, hw, _⟩ := hv
  have hb := sun_six_height_bounds (⟨w, hw⟩ : SunVertex F 200 v)
  have hq := F.q_order
  have hr := F.r_order
  cases v with
  | a q r =>
    simp only [heightQ, heightR, heightS] at hb hs
    rcases hs with h | h | h | h | h | h
    · omega
    · refine ⟨0, r, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart]
      omega
    · omega
    · refine ⟨2, -q-r-1, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart, rotate]
      omega
    · refine ⟨4, q, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart, rotate]
      omega
    · omega
  | b q r =>
    simp only [heightQ, heightR, heightS] at hb hs
    rcases hs with h | h | h | h | h | h
    · refine ⟨3, -r-1, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart, rotate]
      omega
    · omega
    · refine ⟨5, q+r+1, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart, rotate]
      omega
    · omega
    · omega
    · refine ⟨1, -q-1, ?_⟩
      norm_num [Valid, leaf, fromChart, sideChart, rotate]
      omega

theorem leaf_injective {F : Rectangle} {i j : Fin 6} {r s : ℤ}
    (hi : Valid F i r) (hj : Valid F j s) (heq : leaf F i r = leaf F j s) :
    i = j ∧ r = s := by
  have hat : attachment F i r = attachment F j s :=
    noncore_core_neighbor_unique (leaf_not_core (F := F) (i := i) (r := r))
      (attachment_core hi) (attachment_core hj) (leaf_prong F i r)
      (by rw [heq]; exact leaf_prong F j s)
  rw [attachment_eq_point, attachment_eq_point] at hat
  have hp := BoundaryCycle.halfopen_injective F (by decide : 0 ≤ 4)
    (parameter_valid hi).1 (parameter_valid hi).2 (parameter_valid hj).1 (parameter_valid hj).2 hat
  exact ⟨hp.1, by omega⟩

/-- An even ambient walk of at most twenty edges cannot join two distinct
leaf sides: adjacent sides have opposite phases and other sides are too far. -/
theorem short_even_same_side {F : Rectangle} {i j : Fin 6} {r s : ℤ} {n : ℕ}
    (hi : Valid F i r) (hj : Valid F j s)
    (hw : Walk (leaf F i r) (leaf F j s) n) (hn : n ≤ 20) (heven : n % 2 = 0) : i = j := by
  have hq := hw.height_bounds heightQ_lipschitz
  have hr := hw.height_bounds heightR_lipschitz
  have hs := hw.height_bounds heightS_lipschitz
  have hp := hw.heightQ_parity
  have hFq := F.q_order
  have hFr := F.r_order
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | simp only [Valid, leaf, sideChart, fromChart, rotate, heightQ, heightR, heightS] at hi hj hq hr hs hp
    omega

/-- Every actual short even boundary path has a canonical side orientation;
the larger leaf parameter is a right-endpoint candidate. -/
theorem oriented_endpoints {F : Rectangle} (p : BoundaryPath F 200)
    (hn : p.length ≤ 20) (heven : p.length % 2 = 0) :
    ∃ i : Fin 6, ∃ r s : ℤ, Valid F i r ∧ Candidate F i s ∧ r < s ∧
      ((p.start = leaf F i r ∧ p.finish = leaf F i s) ∨
        (p.finish = leaf F i r ∧ p.start = leaf F i s)) := by
  obtain ⟨i, r, hr, hstart⟩ := leaf_coverage p.start_leaf
  obtain ⟨j, s, hs, hfinish⟩ := leaf_coverage p.finish_leaf
  have hw : Walk p.start p.finish p.length := by
    have hh := indexed_subwalk (fun k hk => (p.at_adjacent k hk).1) 0 p.length (by omega)
    simpa only [Nat.zero_add, p.at_start, p.at_finish] using hh
  rw [hstart, hfinish] at hw
  have hij := short_even_same_side hr hs hw hn heven
  subst j
  have hne : r ≠ s := by
    intro heq
    exact p.distinct (hstart.trans (by simpa [heq] using hfinish.symm))
  by_cases hrs : r < s
  · refine ⟨i, r, s, hr, ?_, hrs, Or.inl ⟨hstart,hfinish⟩⟩
    unfold Valid at hr hs
    unfold Candidate
    omega
  · refine ⟨i, s, r, hs, ?_, by omega, Or.inr ⟨hfinish,hstart⟩⟩
    unfold Valid at hr hs
    unfold Candidate
    omega

/-- Global two-edge spacing in both directions, including the cyclic join. -/
theorem candidate_coordinate_spacing {F : Rectangle} {i j : Fin 6} {r s : ℤ}
    (hi : Candidate F i r) (hj : Candidate F j s)
    (hne : (i,r) ≠ (j,s)) :
    let x := BoundaryCycle.coordinate F 0 i (2*r+1)
    let y := BoundaryCycle.coordinate F 0 j (2*s+1)
    (x + 2 ≤ y ∧ y + 2 ≤ x + BoundaryCycle.perimeter F 0) ∨
      (y + 2 ≤ x ∧ x + 2 ≤ y + BoundaryCycle.perimeter F 0) := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;>
    norm_num [Candidate, BoundaryCycle.coordinate, BoundaryCycle.offset,
      BoundaryCycle.perimeter, BoundaryCycle.baseLength, BoundaryCycle.width,
      BoundaryCycle.height, BoundaryCycle.lower, sideChart, Prod.mk.injEq] at * <;> omega

end BoundaryLeaves
end RootedKP.Honeycomb
