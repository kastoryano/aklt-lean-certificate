import RootedKP.Target
import RootedKP.Arithmetic
import RootedKP.PolymerLength

/-!
# From actual polymer activities to the arithmetic envelopes

This is a weight comparison for the actual polymers, independent of any
unproved counting table. Their required minimum length is proved separately.
-/

namespace RootedKP.AKLT

open scoped ENNReal NNReal

theorem polymer_budget_le_bare {F : Honeycomb.Rectangle} (p : Polymer F) :
    (p.activity : ℝ) * Real.exp p.cost ≤
      (3 / (3 : ℝ) ^ p.length) * Real.exp ((p.length : ℝ) / 500 + p.cost) := by
  have hf : (if p.kind = .path then (5 / 6 : ℝ) else 1) ≤ 1 := by
    split_ifs <;> norm_num
  change ((if p.kind = .path then (5 / 6 : ℝ) else 1) *
    (3 / (3 : ℝ) ^ p.length) * Real.exp ((p.length : ℝ) / 500)) *
    Real.exp p.cost ≤ _
  rw [Real.exp_add]
  calc
    _ = (if p.kind = .path then (5 / 6 : ℝ) else 1) *
      ((3 / (3 : ℝ) ^ p.length) *
        (Real.exp ((p.length : ℝ) / 500) * Real.exp p.cost)) := by ring
    _ ≤ 1 * ((3 / (3 : ℝ) ^ p.length) *
        (Real.exp ((p.length : ℝ) / 500) * Real.exp p.cost)) := by
      exact mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := one_mul _

theorem bare_weight_le_weightCap {F : Honeycomb.Rectangle} (p : Polymer F) :
    (3 / (3 : ℝ) ^ p.length) * Real.exp ((p.length : ℝ) / 500 + p.cost) ≤
      (Arithmetic.weightCap p.length : ℝ) := by
  have hlen := p.length_ge_three
  rcases (show p.length = 3 ∨ p.length = 4 ∨ p.length = 5 ∨
      p.length = 6 ∨ 7 ≤ p.length by omega) with h | h | h | h | h
  · convert Arithmetic.exp_weight3_bound using 1 <;>
      norm_num [Polymer.cost, h] <;> ring
  · convert Arithmetic.exp_weight4_bound using 1 <;>
      norm_num [Polymer.cost, h] <;> ring
  · convert Arithmetic.exp_weight5_bound using 1 <;>
      norm_num [Polymer.cost, h] <;> ring
  · convert Arithmetic.exp_weight6_bound using 1 <;>
      norm_num [Polymer.cost, h] <;> ring
  · have hc : p.cost = (17 / 100 : ℝ) * p.length := by
      unfold Polymer.cost
      split <;> first | omega | rfl
    rw [hc, Arithmetic.weightCap_eq_long _ h]
    push_cast
    rw [show (p.length : ℝ) / 500 + 17 / 100 * p.length =
      (p.length : ℝ) * (43 / 250) by ring]
    convert Arithmetic.long_weight_bound p.length using 1 <;> ring

theorem polymer_budget_le_weightCap {F : Honeycomb.Rectangle} (p : Polymer F) :
    (p.activity : ℝ) * Real.exp p.cost ≤ (Arithmetic.weightCap p.length : ℝ) :=
  (polymer_budget_le_bare p).trans (bare_weight_le_weightCap p)

/-- Retain the improved path factor used by the scalar certificate. -/
theorem path_budget_le_weightCap {F : Honeycomb.Rectangle} (p : Polymer F)
    (hk : p.kind = .path) :
    (p.activity : ℝ) * Real.exp p.cost ≤
      (5 / 6 : ℝ) * (Arithmetic.weightCap p.length : ℝ) := by
  have heq : (p.activity : ℝ) * Real.exp p.cost =
      (5 / 6 : ℝ) * ((3 / (3 : ℝ) ^ p.length) *
        Real.exp ((p.length : ℝ) / 500 + p.cost)) := by
    change ((if p.kind = .path then (5 / 6 : ℝ) else 1) *
      (3 / (3 : ℝ) ^ p.length) * Real.exp ((p.length : ℝ) / 500)) *
      Real.exp p.cost = _
    rw [if_pos hk, Real.exp_add]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (bare_weight_le_weightCap p) (by norm_num)

theorem rootBudget_le_weightCap {F : Honeycomb.Rectangle} (p : Polymer F)
    :
    rootBudget p ≤ ENNReal.ofReal (Arithmetic.weightCap p.length : ℝ) :=
  ENNReal.ofReal_le_ofReal (polymer_budget_le_weightCap p)

theorem rootBudget_path_le_weightCap {F : Honeycomb.Rectangle} (p : Polymer F)
    (hk : p.kind = .path) :
    rootBudget p ≤ ENNReal.ofReal ((5 / 6 : ℝ) * (Arithmetic.weightCap p.length : ℝ)) :=
  ENNReal.ofReal_le_ofReal (path_budget_le_weightCap p hk)

end RootedKP.AKLT
