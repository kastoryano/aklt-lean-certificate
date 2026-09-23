import RootedKP.BoundaryCycle

namespace RootedKP.Honeycomb.BoundaryCycle

abbrev baseLength (d : ℕ) : ℤ := 401 - 2 * d
abbrev width (F : Rectangle) : ℤ := F.qmax - F.qmin
abbrev height (F : Rectangle) : ℤ := F.rmax - F.rmin

def offset (F : Rectangle) (d : ℕ) (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 0
  | 1 => baseLength d + 2 * height F
  | 2 => 2 * baseLength d + 2 * height F
  | 3 => 3 * baseLength d + 2 * height F + 2 * width F
  | 4 => 4 * baseLength d + 4 * height F + 2 * width F
  | _ => 5 * baseLength d + 4 * height F + 2 * width F

def perimeter (F : Rectangle) (d : ℕ) : ℤ :=
  6 * baseLength d + 4 * width F + 4 * height F

def coordinate (F : Rectangle) (d : ℕ) (i : Fin 6) (τ : ℤ) : ℤ :=
  offset F d i + τ - lower F d i

theorem perimeter_positive (F : Rectangle) {d : ℕ} (hd : d ≤ 4) : 0 < perimeter F d := by
  have hq := F.q_order
  have hr := F.r_order
  dsimp only [perimeter, baseLength, width, height]
  omega

theorem coordinate_range (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (i : Fin 6) {τ : ℤ}
    (hl : lower F d i ≤ τ) (hu : τ < upper F i) :
    0 ≤ coordinate F d i τ ∧ coordinate F d i τ < perimeter F d := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;>
    simp only [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega

theorem coordinate_injective (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F d j ≤ σ) (hσ₁ : σ < upper F j)
    (heq : coordinate F d i τ = coordinate F d j σ) : i = j ∧ τ = σ := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;>
    simp only [coordinate, offset, baseLength, width, height, lower, upper, sideChart] at hτ₀ hτ₁ hσ₀ hσ₁ heq <;>
    constructor <;> first | rfl | omega

/-- These six intervals fill the complete integer circle without gaps. -/
theorem coordinate_surjective (F : Rectangle) {d : ℕ} (hd : d ≤ 4) {x : ℤ}
    (hx : 0 ≤ x ∧ x < perimeter F d) :
    ∃ i : Fin 6, ∃ τ : ℤ, lower F d i ≤ τ ∧ τ < upper F i ∧ coordinate F d i τ = x := by
  have hq := F.q_order
  have hr := F.r_order
  by_cases h1 : x < offset F d (1 : Fin 6)
  · refine ⟨0, lower F d 0 + x - offset F d 0, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega
  by_cases h2 : x < offset F d (2 : Fin 6)
  · refine ⟨1, lower F d 1 + x - offset F d 1, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega
  by_cases h3 : x < offset F d (3 : Fin 6)
  · refine ⟨2, lower F d 2 + x - offset F d 2, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega
  by_cases h4 : x < offset F d (4 : Fin 6)
  · refine ⟨3, lower F d 3 + x - offset F d 3, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega
  by_cases h5 : x < offset F d (5 : Fin 6)
  · refine ⟨4, lower F d 4 + x - offset F d 4, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega
  refine ⟨5, lower F d 5 + x - offset F d 5, ?_, ?_, ?_⟩ <;>
      norm_num [coordinate, offset, perimeter, baseLength, width, height, lower, upper, sideChart] at * <;> omega

theorem coordinate_successor (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {τ : ℤ} (hl : lower F d i ≤ τ) (hu : τ < upper F i) :
    coordinate F d (successorSide F i τ) (successorParameter F d i τ) =
      if coordinate F d i τ + 1 = perimeter F d then 0 else coordinate F d i τ + 1 := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;>
    simp only [successorSide, successorParameter, coordinate, offset, perimeter,
      baseLength, width, height, lower, upper, sideChart, nextSide] at * <;>
    split_ifs <;> norm_num [offset] <;> omega

/-- Linear coordinates lose between zero and `12d` under the exact boundary
retraction. This is the non-wrapping arc-preimage estimate. -/
theorem retraction_coordinate_loss (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {τ : ℤ} (hl : lower F 0 i ≤ τ) (hu : τ < upper F i) :
    let x := coordinate F 0 i τ
    let y := coordinate F d i (clamp (lower F d i) (upper F i) τ)
    y ≤ x ∧ x ≤ y + 12 * d := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;>
    simp only [coordinate, offset, baseLength, width, height, lower, upper, sideChart, clamp,
      max_def, min_def] at * <;> split_ifs <;> omega

theorem preimage_of_nonwrapping_arc (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {τ lo hi : ℤ} (hl : lower F 0 i ≤ τ) (hu : τ < upper F i)
    (hy : lo ≤ coordinate F d i (clamp (lower F d i) (upper F i) τ) ∧
      coordinate F d i (clamp (lower F d i) (upper F i) τ) ≤ hi) :
    lo ≤ coordinate F 0 i τ ∧ coordinate F 0 i τ ≤ hi + 12 * d := by
  have hh := retraction_coordinate_loss F hd i hl hu
  dsimp only at hh
  omega

end RootedKP.Honeycomb.BoundaryCycle
