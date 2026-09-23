import RootedKP.AbstractKP
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Basic.ENNReal.BigOperators

/-!
# KP recursion and passage to the full sum in extended nonnegative reals

There is no convergence assumption in these statements. The combinatorial
module must supply the product recursion for the actual truncated heap sums.
-/

namespace RootedKP

open scoped BigOperators ENNReal

namespace KPData

variable {P : Type*} (K : KPData P)

theorem ennreal_product_le_budget (f : P → ℝ≥0∞)
    (hbound : ∀ p, f p ≤ ENNReal.ofReal (K.budget p)) (p : P) :
    ENNReal.ofReal (K.activity p) * ∏ q ∈ K.neighbours p, (1 + f q) ≤
      ENNReal.ofReal (K.budget p) := by
  calc
    ENNReal.ofReal (K.activity p) * ∏ q ∈ K.neighbours p, (1 + f q) ≤
        ENNReal.ofReal (K.activity p) *
          ∏ q ∈ K.neighbours p, (1 + ENNReal.ofReal (K.budget q)) := by
      exact mul_le_mul le_rfl
        (Finset.prod_le_prod (fun q _ => add_le_add le_rfl (hbound q)))
        zero_le zero_le
    _ = ENNReal.ofReal (K.activity p * ∏ q ∈ K.neighbours p, (1 + K.budget q)) := by
      rw [ENNReal.ofReal_mul (K.activity_nonneg p),
        ENNReal.ofReal_prod_of_nonneg (fun q _ => add_nonneg zero_le_one (K.budget_nonneg q))]
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      rw [ENNReal.ofReal_add zero_le_one (K.budget_nonneg q), ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (K.budget p) :=
      ENNReal.ofReal_le_ofReal
        (K.product_le_budget K.budget K.budget_nonneg (fun _ => le_rfl) p)

theorem ennreal_mass_le_budget_of_product_recursion (mass : ℕ → P → ℝ≥0∞)
    (hzero : ∀ p, mass 0 p = 0)
    (hstep : ∀ n p, mass (n + 1) p ≤ ENNReal.ofReal (K.activity p) *
      ∏ q ∈ K.neighbours p, (1 + mass n q)) :
    ∀ n p, mass n p ≤ ENNReal.ofReal (K.budget p) := by
  intro n
  induction n with
  | zero => intro p; rw [hzero p]; exact zero_le
  | succ n ih => intro p; exact (hstep n p).trans (K.ennreal_product_le_budget _ ih p)

end KPData

/-- Every finite set of objects is contained in a common size truncation.
Consequently a uniform bound on the truncated sums bounds the full sum, even
if a truncation contains infinitely many objects. -/
theorem tsum_le_of_bounded_size {H : Type*} (size : H → ℕ) (w : H → ℝ≥0∞)
    {B : ℝ≥0∞} (hbound : ∀ n, (∑' h : {h : H // size h ≤ n}, w h) ≤ B) :
    (∑' h, w h) ≤ B := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let N := s.sup size
  have hmem : ∀ h ∈ s, size h ≤ N := fun h hh => Finset.le_sup hh
  calc
    (∑ h ∈ s, w h) = ∑ h ∈ s, if size h ≤ N then w h else 0 := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [hmem h hh]
    _ ≤ ∑' h, if size h ≤ N then w h else 0 := ENNReal.sum_le_tsum s
    _ = ∑' h : {h : H // size h ≤ N}, w h := by
      convert! (tsum_subtype {h : H | size h ≤ N} w).symm using 1
      apply tsum_congr
      intro h
      by_cases hh : size h ≤ N <;> simp [Set.indicator, hh]
    _ ≤ B := hbound N

end RootedKP
