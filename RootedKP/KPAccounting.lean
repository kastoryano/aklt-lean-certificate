import RootedKP.ArithmeticBounds
import RootedKP.ActivityBounds
import RootedKP.AKLTApplication

/-!
# Final scalar accounting for the literal AKLT KP sum

The inputs below concern separate path and loop masses, with explicit
allowances computed from the count tables. These inputs remain to be proved
from the graph enumeration and geometric counting; no KP conclusion is an
assumed field or an axiom.
-/

namespace RootedKP.AKLT

open scoped BigOperators ENNReal NNReal Classical
open Arithmetic

set_option maxHeartbeats 0

noncomputable def realBudget {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ :=
  (p.activity : ℝ) * Real.exp p.cost

theorem realBudget_nonneg {F : Honeycomb.Rectangle} (p : Polymer F) :
    0 ≤ realBudget p := mul_nonneg p.activity.property (Real.exp_pos _).le

noncomputable def kindSet {F : Honeycomb.Rectangle} (p : Polymer F) (kind : Kind) :
    Finset (Polymer F) :=
  Finset.univ.filter (fun q => q.kind = kind ∧ Polymer.Incompatible q p)

noncomputable def kindMass {F : Honeycomb.Rectangle} (p : Polymer F) (kind : Kind) : ℝ :=
  ∑ q ∈ kindSet p kind, realBudget q

def shortCounts (n : ℕ) : List ℕ :=
  match n with
  | 3 => W3Counts
  | 4 => W4Counts
  | 5 => W5Counts
  | 6 => W6Counts
  | _ => []

def pathAllowance {F : Honeycomb.Rectangle} (p : Polymer F) : ℚ :=
  if p.length ≤ 6 then
    if p.kind = .path then
      pathFactor * (sumCounts weightCap 3 1 (shortCounts p.length) +
        boundaryTail + ((p.length : ℚ) - 2) * interiorTail)
    else pathFactor * (sumCounts weightCap 3 1 L6Counts + 6 * interiorTail)
  else pathFactor * (longFiniteUniformAllowance p.length + (p.length : ℚ) * interiorTail)

def loopAllowance {F : Honeycomb.Rectangle} (p : Polymer F) : ℚ :=
  (if p.kind = .path then (p.length : ℚ) - 2 else (p.length : ℚ)) * loopMass

theorem cost_eq_arithmetic {F : Honeycomb.Rectangle} (p : Polymer F) :
    p.cost = (a p.length : ℝ) := by
  unfold Polymer.cost a
  split <;> simp_all [slope]

theorem loopMass_nonneg : 0 ≤ loopMass := by
  norm_num [loopMass, sumCounts, loopCounts, weightCap, rCap, qCap]

theorem allowance_le_cost {F : Honeycomb.Rectangle} (p : Polymer F) :
    pathAllowance p + loopAllowance p ≤ a p.length := by
  by_cases hs : p.length ≤ 6
  · cases hk : p.kind with
    | path =>
        have hmin := p.length_ge_three
        rcases (show p.length = 3 ∨ p.length = 4 ∨ p.length = 5 ∨ p.length = 6 by omega)
            with hn | hn | hn | hn
        · simpa [pathAllowance, loopAllowance, shortCounts, hk, hn, shortPathAllowance]
            using W3_allowance
        · simpa [pathAllowance, loopAllowance, shortCounts, hk, hn, shortPathAllowance]
            using W4_allowance
        · simpa [pathAllowance, loopAllowance, shortCounts, hk, hn, shortPathAllowance]
            using W5_allowance
        · simpa [pathAllowance, loopAllowance, shortCounts, hk, hn, shortPathAllowance]
            using W6_allowance
    | loop =>
        have hn : p.length = 6 := le_antisymm hs (p.loop_length_ge_six hk)
        simpa [pathAllowance, loopAllowance, hk, hn, shortLoopAllowance] using L6_allowance
  · have hn : 7 ≤ p.length := by omega
    have hl : loopAllowance p ≤ (p.length : ℚ) * loopMass := by
      unfold loopAllowance
      split_ifs
      · have h := loopMass_nonneg
        nlinarith
      · exact le_rfl
    have ha : a p.length = slope * p.length := by
      unfold a
      split <;> first | omega | rfl
    calc
      pathAllowance p + loopAllowance p ≤ longUniformAllowance p.length := by
        rw [pathAllowance, if_neg hs]
        exact add_le_add le_rfl hl
      _ ≤ slope * (p.length : ℚ) := longUniformAllowance_le_cost _ (by positivity)
      _ = a p.length := ha.symm

theorem incompatible_sum_eq_kind_masses {F : Honeycomb.Rectangle} (p : Polymer F) :
    (∑ q ∈ Finset.univ.filter (fun q => Polymer.Incompatible q p), realBudget q) =
      kindMass p .path + kindMass p .loop := by
  classical
  simp only [kindMass, kindSet, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  cases hk : q.kind <;> by_cases hi : Polymer.Incompatible q p <;> simp [hk, hi]

/-- The graph-counting inputs are separate and concrete; this theorem supplies
the entire scalar-arithmetic connection to the exact model KP proposition. -/
theorem uniformKP_of_kind_mass_bounds
    (hpath : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
      kindMass p .path ≤ (pathAllowance p : ℝ))
    (hloop : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
      kindMass p .loop ≤ (loopAllowance p : ℝ)) : UniformKPCondition := by
  classical
  intro F p
  have hreal : (∑ q ∈ Finset.univ.filter (fun q => Polymer.Incompatible q p),
      realBudget q) ≤ p.cost := by
    rw [incompatible_sum_eq_kind_masses, cost_eq_arithmetic]
    have hc : ((pathAllowance p + loopAllowance p : ℚ) : ℝ) ≤ (a p.length : ℝ) := by
      exact_mod_cast allowance_le_cost p
    push_cast at hc
    exact (add_le_add (hpath F p) (hloop F p)).trans hc
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => realBudget_nonneg q)] at h
  rw [tsum_fintype]
  simpa only [Finset.sum_filter, realBudget,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal] using h

end RootedKP.AKLT
