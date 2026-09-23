import RootedKP.CollarCells
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! A canonical, duplicate-free traversal of the six exact boundary zigzags.
The last point of each closed side is the first point of the next side. -/
namespace RootedKP.Honeycomb
namespace BoundaryCycle

abbrev lower (F : Rectangle) (d : ℕ) (i : Fin 6) : ℤ :=
  2 * ((sideChart F 200 i).r₀ + d) - 1
abbrev upper (F : Rectangle) (i : Fin 6) : ℤ := 2 * (sideChart F 200 i).r₁

def point (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ) : Vertex :=
  fromChart i (vertexAt ((sideChart F 200 i).Q - d) τ)

theorem range_nonempty (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (i : Fin 6) :
    lower F d i < upper F i := by
  have hh := sideChart_inner_nonempty F d hd i
  dsimp only [lower, upper]
  omega

theorem point_in_cell (F : Rectangle) (d : ℕ) (i : Fin 6) {τ : ℤ}
    (hl : lower F d i ≤ τ) (hu : τ ≤ upper F i) :
    GlobalCell F 200 d i (point F d i τ) := by
  unfold GlobalCell point
  rw [toChart_fromChart]
  unfold vertexAt
  split_ifs <;> simp only [InCell] <;> dsimp only [lower, upper] at hl hu <;> omega

theorem point_injective (F : Rectangle) (d : ℕ) (i : Fin 6) :
    Function.Injective (point F d i) := by
  intro x y h
  have hh := congrArg (fun v => heightR (toChart i v)) h
  simpa only [point, toChart_fromChart, vertexAt_height] using hh

theorem point_adjacent (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ) :
    Adj (point F d i τ) (point F d i (τ + 1)) :=
  fromChart_adj i (vertexAt_adjacent _ _)

/-- The phase-correct identification at all six joints, including the wrap. -/
theorem joint (F : Rectangle) (d : ℕ) (i : Fin 6) :
    point F d i (upper F i) = point F d (nextSide i) (lower F d (nextSide i)) := by
  unfold point lower upper
  rw [fromChart_next, sideChart_next_Q, sideChart_next_r₀,
    vertexAt_even, vertexAt_lower_endpoint]
  congr 1
  simp only [rotate]
  congr 1 <;> omega

/-- An inner-side point can meet the next cell only at its terminal joint. -/
theorem next_cell_only_at_joint (F : Rectangle) {d : ℕ} (i : Fin 6) {τ : ℤ}
    (hl : lower F d i ≤ τ) (hu : τ ≤ upper F i)
    (hnext : GlobalCell F 200 d (nextSide i) (point F d i τ)) : τ = upper F i := by
  have hcur := point_in_cell F d i hl hu
  dsimp only [GlobalCell] at hcur hnext
  rw [toChart_next, sideChart_next_Q, sideChart_next_r₀] at hnext
  simp only [point, toChart_fromChart] at hcur hnext
  unfold vertexAt at hnext
  split_ifs at hnext <;> simp only [inverseRotate, InCell] at hnext <;>
    dsimp only [upper] at hu ⊢ <;> omega

/-- Half-open side parameters have no duplication, even across corners. -/
theorem halfopen_injective (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    {i j : Fin 6} {τ σ : ℤ}
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F d j ≤ σ) (hσ₁ : σ < upper F j)
    (heq : point F d i τ = point F d j σ) : i = j ∧ τ = σ := by
  have hi := point_in_cell F d i hτ₀ hτ₁.le
  have hj := point_in_cell F d j hσ₀ hσ₁.le
  have hj' : GlobalCell F 200 d j (point F d i τ) := heq ▸ hj
  rcases globalCell_overlap_same_or_adjacent hd hi hj' with hij | hij
  · subst j
    exact ⟨rfl, point_injective F d i heq⟩
  · rcases hij with hij | hij
    · have hn : nextSide i = j := Fin.ext hij
      have hh := next_cell_only_at_joint F i hτ₀ hτ₁.le (hn.symm ▸ hj')
      omega
    · have hn : nextSide j = i := Fin.ext hij
      have hi' : GlobalCell F 200 d i (point F d j σ) := heq ▸ hi
      have hh := next_cell_only_at_joint F j hσ₀ hσ₁.le (hn.symm ▸ hi')
      omega

/-- Every literal inner-boundary vertex has one canonical half-open side. -/
theorem inner_iff_halfopen (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (v : Vertex) :
    InnerBoundary F d v ↔
      ∃ i : Fin 6, ∃ τ : ℤ, lower F d i ≤ τ ∧ τ < upper F i ∧ v = point F d i τ := by
  constructor
  · rintro ⟨i, τ, hl, hu, rfl⟩
    by_cases hlt : τ < upper F i
    · exact ⟨i, τ, hl, hlt, rfl⟩
    · have hu' : τ ≤ upper F i := hu
      have heq : τ = upper F i := by omega
      refine ⟨nextSide i, lower F d (nextSide i), le_refl _, range_nonempty F hd _, ?_⟩
      change point F d i τ = _
      rw [heq]
      exact joint F d i
  · rintro ⟨i, τ, hl, hu, rfl⟩
    exact ⟨i, τ, hl, hu.le, rfl⟩

/-- The next vertex is on the same side, except at its final edge, where
it becomes the initial point of the next side. -/
def successorSide (F : Rectangle) (i : Fin 6) (τ : ℤ) : Fin 6 :=
  if τ + 1 < upper F i then i else nextSide i

def successorParameter (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ) : ℤ :=
  if τ + 1 < upper F i then τ + 1 else lower F d (nextSide i)

theorem successor_valid (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (i : Fin 6) {τ : ℤ}
    (hl : lower F d i ≤ τ) (hu : τ < upper F i) :
    lower F d (successorSide F i τ) ≤ successorParameter F d i τ ∧
      successorParameter F d i τ < upper F (successorSide F i τ) := by
  unfold successorSide successorParameter
  split_ifs with h
  · omega
  · exact ⟨le_refl _, range_nonempty F hd _⟩

theorem successor_adjacent (F : Rectangle) (d : ℕ) (i : Fin 6) {τ : ℤ}
    (hu : τ < upper F i) :
    Adj (point F d i τ)
      (point F d (successorSide F i τ) (successorParameter F d i τ)) := by
  unfold successorSide successorParameter
  split_ifs with h
  · exact point_adjacent F d i τ
  · rw [← joint]
    have hh : upper F i = τ + 1 := by omega
    rw [hh]
    exact point_adjacent F d i τ

/-- The global retraction has the explicit clamp formula on the outer cycle. -/
theorem retraction_outer_point (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {τ : ℤ} (hl : lower F 0 i ≤ τ) (hu : τ ≤ upper F i) :
    collarMap F d (point F 0 i τ) =
      point F d i (clamp (lower F d i) (upper F i) τ) := by
  have hc : GlobalCell F 200 d i (point F 0 i τ) := by
    unfold GlobalCell point
    rw [toChart_fromChart]
    unfold vertexAt
    split_ifs <;> simp only [InCell] <;> dsimp only [lower, upper] at hl hu <;> omega
  rw [collarMap_on_cell hd hc]
  simp only [chartImage, point, toChart_fromChart, localMap, vertexAt_height]

theorem successor_point (F : Rectangle) (d : ℕ) (i : Fin 6) {τ : ℤ}
    (hu : τ < upper F i) :
    point F d (successorSide F i τ) (successorParameter F d i τ) = point F d i (τ + 1) := by
  unfold successorSide successorParameter
  split_ifs with h
  · rfl
  · rw [← joint]
    congr 1
    omega

/-- Precisely the first `2d` outgoing edges of each outer side collapse. -/
theorem outer_edge_collapsed_iff (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {τ : ℤ} (hl : lower F 0 i ≤ τ) (hu : τ < upper F i) :
    (collarMap F d (point F 0 i τ) =
      collarMap F d (point F 0 (successorSide F i τ) (successorParameter F 0 i τ))) ↔
      τ < lower F d i := by
  rw [successor_point F 0 i hu,
    retraction_outer_point F hd i hl hu.le,
    retraction_outer_point F hd i (by omega : lower F 0 i ≤ τ + 1) (by omega)]
  rw [(point_injective F d i).eq_iff]
  have hn := range_nonempty F hd i
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

def collapsedParameters (F : Rectangle) (d : ℕ) (i : Fin 6) : Finset ℤ :=
  Finset.Ico (lower F 0 i) (lower F d i)

theorem collapsedParameters_card (F : Rectangle) (d : ℕ) (i : Fin 6) :
    (collapsedParameters F d i).card = 2 * d := by
  rw [collapsedParameters, Int.card_Ico]
  dsimp only [lower]
  omega

theorem collapsedParameters_exact (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) (τ : ℤ) : τ ∈ collapsedParameters F d i ↔
    lower F 0 i ≤ τ ∧ τ < upper F i ∧
      collarMap F d (point F 0 i τ) =
        collarMap F d (point F 0 (successorSide F i τ) (successorParameter F 0 i τ)) := by
  simp only [collapsedParameters, Finset.mem_Ico]
  constructor
  · rintro ⟨hl, hu⟩
    have htop : τ < upper F i := lt_trans hu (range_nonempty F hd i)
    exact ⟨hl, htop, (outer_edge_collapsed_iff F hd i hl htop).mpr hu⟩
  · rintro ⟨hl, hu, heq⟩
    exact ⟨hl, (outer_edge_collapsed_iff F hd i hl hu).mp heq⟩

/-- Exact count of collapsed oriented cycle edges across the six disjoint
half-open side parameter sets. -/
theorem collapsed_total (F : Rectangle) (d : ℕ) :
    (∑ i : Fin 6, (collapsedParameters F d i).card) = 12 * d := by
  simp [collapsedParameters_card]
  omega

end BoundaryCycle
end RootedKP.Honeycomb
