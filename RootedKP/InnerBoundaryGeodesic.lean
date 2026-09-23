import RootedKP.PathConfinement
import RootedKP.BoundaryCycleAdjacency

namespace RootedKP.Honeycomb

/-- An actual ambient walk all of whose vertices satisfy a given predicate. -/
inductive WalkOn (P : Vertex → Prop) : Vertex → Vertex → ℕ → Prop
  | nil (u : Vertex) (hu : P u) : WalkOn P u u 0
  | cons {u v w : Vertex} {n : ℕ} (hu : P u) (he : Adj u v)
      (tail : WalkOn P v w n) : WalkOn P u w (n+1)

theorem WalkOn.start_mem {P : Vertex → Prop} {u v : Vertex} {n : ℕ} (h : WalkOn P u v n) : P u := by
  cases h with
  | nil _ hu => exact hu
  | cons hu _ _ => exact hu

theorem WalkOn.finish_mem {P : Vertex → Prop} {u v : Vertex} {n : ℕ} (h : WalkOn P u v n) : P v := by
  induction h with
  | nil _ hu => exact hu
  | cons _ _ _ ih => exact ih

theorem WalkOn.toWalk {P : Vertex → Prop} {u v : Vertex} {n : ℕ} (h : WalkOn P u v n) : Walk u v n := by
  induction h with
  | nil u _ => exact Walk.nil u
  | cons _ he _ ih => exact Walk.cons he ih

theorem WalkOn.append {P : Vertex → Prop} {u v w : Vertex} {n m : ℕ}
    (h : WalkOn P u v n) (h' : WalkOn P v w m) : WalkOn P u w (n+m) := by
  induction h with
  | nil => simpa using h'
  | cons hu he _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WalkOn.cons hu he (ih h')

theorem WalkOn.reverse {P : Vertex → Prop} {u v : Vertex} {n : ℕ}
    (h : WalkOn P u v n) : WalkOn P v u n := by
  induction h with
  | nil u hu => exact WalkOn.nil u hu
  | cons hu he tail ih =>
    exact ih.append (WalkOn.cons tail.start_mem (adj_symm he) (WalkOn.nil _ hu))

theorem Walk.map {u v : Vertex} {n : ℕ} (h : Walk u v n) (f : Vertex → Vertex)
    (hf : ∀ a b, Adj a b → Adj (f a) (f b)) : Walk (f u) (f v) n := by
  induction h with
  | nil u => exact Walk.nil _
  | cons he _ ih => exact Walk.cons (hf _ _ he) ih

namespace BoundaryCycle

private theorem point_mem (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ)
    (hl : lower F d i ≤ τ) (hu : τ ≤ upper F i) : InnerBoundary F d (point F d i τ) :=
  ⟨i,τ,hl,hu,rfl⟩

theorem point_walk_steps (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ) (k : ℕ)
    (hl : lower F d i ≤ τ) (hu : τ+k ≤ upper F i) :
    WalkOn (InnerBoundary F d) (point F d i τ) (point F d i (τ+k)) k := by
  induction k generalizing τ with
  | zero => simpa using WalkOn.nil _ (point_mem F d i τ hl (by simpa using hu))
  | succ k ih =>
    have ht := ih (τ+1) (by omega) (by push_cast at *; omega)
    have hh := WalkOn.cons (point_mem F d i τ hl (by push_cast at *; omega))
      (point_adjacent F d i τ) ht
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hh

theorem same_side_geodesic (F : Rectangle) (d : ℕ) (i : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ ≤ upper F i)
    (hσ₀ : lower F d i ≤ σ) (hσ₁ : σ ≤ upper F i)
    {n : ℕ} (hw : Walk (point F d i τ) (point F d i σ) n) :
    ∃ m ≤ n, WalkOn (InnerBoundary F d) (point F d i τ) (point F d i σ) m := by
  have hb := (hw.map (toChart i) (fun _ _ => toChart_adj i)).height_bounds heightR_lipschitz
  simp only [point, toChart_fromChart, vertexAt_height] at hb
  by_cases hh : τ ≤ σ
  · refine ⟨(σ-τ).toNat, by omega, ?_⟩
    have heq : τ + (σ-τ).toNat = σ := by omega
    simpa only [heq] using point_walk_steps F d i τ (σ-τ).toNat hτ₀ (by omega)
  · refine ⟨(τ-σ).toNat, by omega, ?_⟩
    have heq : σ + (τ-σ).toNat = τ := by omega
    have h := point_walk_steps F d i σ (τ-σ).toNat hσ₀ (by omega)
    simpa only [heq] using h.reverse

private theorem rotated_height (Q τ : ℤ) : heightR (rotate (vertexAt Q τ)) = τ+2*Q+1 := by
  obtain ⟨r, h⟩ : ∃ r : ℤ, τ = 2*r ∨ τ = 2*r+1 := ⟨τ/2, by omega⟩
  rcases h with rfl | rfl <;> simp only [vertexAt_even, vertexAt_odd, rotate, heightR] <;> omega

/-- The complete chain across one corner is calibrated by a single global
one-Lipschitz height, so replacing a walk by that chain never adds edges. -/
theorem next_side_geodesic (F : Rectangle) (d : ℕ) (i : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ ≤ upper F i)
    (hσ₀ : lower F d (nextSide i) ≤ σ) (hσ₁ : σ ≤ upper F (nextSide i))
    {n : ℕ} (hw : Walk (point F d i τ) (point F d (nextSide i) σ) n) :
    ∃ m ≤ n, WalkOn (InnerBoundary F d) (point F d i τ) (point F d (nextSide i) σ) m := by
  have hb := (hw.map (toChart i) (fun _ _ => toChart_adj i)).height_bounds heightR_lipschitz
  simp only [point, fromChart_next, toChart_fromChart, vertexAt_height, rotated_height,
    sideChart_next_Q] at hb
  have hn : upper F i-τ + (σ-lower F d (nextSide i)) ≤ n := by
    dsimp only [lower, upper]
    rw [sideChart_next_r₀]
    omega
  let m₁ := (upper F i-τ).toNat
  let m₂ := (σ-lower F d (nextSide i)).toNat
  have h₁ : τ + m₁ = upper F i := by dsimp [m₁]; omega
  have h₂ : lower F d (nextSide i)+m₂ = σ := by dsimp [m₂]; omega
  have w₁ := point_walk_steps F d i τ m₁ hτ₀ (by omega)
  have w₂ := point_walk_steps F d (nextSide i) (lower F d (nextSide i)) m₂ (le_refl _) (by omega)
  rw [h₁, joint] at w₁
  rw [h₂] at w₂
  refine ⟨m₁+m₂, ?_, w₁.append w₂⟩
  dsimp only [m₁,m₂]
  omega

set_option maxHeartbeats 1000000 in
/-- Short walks cannot reach nonadjacent inner sides, uniformly in both
rectangle dimensions. This uses the literal primal height bounds. -/
theorem short_walk_side_pairs (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F d j ≤ σ) (hσ₁ : σ < upper F j)
    {n : ℕ} (hw : Walk (point F d i τ) (point F d j σ) n) (hn : n ≤ 86) :
    i = j ∨ j = nextSide i ∨ i = nextSide j := by
  have hq := hw.height_bounds heightQ_lipschitz
  have hr := hw.height_bounds heightR_lipschitz
  have hs := hw.height_bounds heightS_lipschitz
  have hFq := F.q_order
  have hFr := F.r_order
  obtain ⟨a, ha⟩ : ∃ a : ℤ, τ = 2*a ∨ τ = 2*a+1 := ⟨τ/2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, σ = 2*b ∨ σ = 2*b+1 := ⟨σ/2, by omega⟩
  fin_cases i <;> fin_cases j <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [point, fromChart, sideChart, lower, upper, nextSide,
      vertexAt_even, vertexAt_odd, rotate, heightQ, heightR, heightS] at * <;> omega

/-- Every actual short interior excursion between inner-boundary vertices
has a boundary replacement of no greater length. -/
theorem short_walk_boundary_replacement {F : Rectangle} {d n : ℕ} (hd : d ≤ 4)
    {u v : Vertex} (hu : InnerBoundary F d u) (hv : InnerBoundary F d v)
    (hw : Walk u v n) (hn : n ≤ 86) :
    ∃ m ≤ n, WalkOn (InnerBoundary F d) u v m := by
  obtain ⟨i,τ,hτ₀,hτ₁,rfl⟩ := (inner_iff_halfopen F hd u).mp hu
  obtain ⟨j,σ,hσ₀,hσ₁,rfl⟩ := (inner_iff_halfopen F hd v).mp hv
  rcases short_walk_side_pairs F hd i j τ σ hτ₀ hτ₁ hσ₀ hσ₁ hw hn with h | h | h
  · subst j
    exact same_side_geodesic F d i τ σ hτ₀ hτ₁.le hσ₀ hσ₁.le hw
  · subst j
    exact next_side_geodesic F d i τ σ hτ₀ hτ₁.le hσ₀ hσ₁.le hw
  · subst i
    obtain ⟨m,hm,hwalk⟩ := next_side_geodesic F d j σ τ hσ₀ hσ₁.le hτ₀ hτ₁.le hw.reverse
    exact ⟨m,hm,hwalk.reverse⟩

end BoundaryCycle
end RootedKP.Honeycomb
