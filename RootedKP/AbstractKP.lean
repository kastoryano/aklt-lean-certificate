import Mathlib.Analysis.Complex.Exponential

/-!
# The numerical induction in the rooted heap KP bound

This file proves the product-recursion implication.  Its hypotheses explicitly
include a finite-size recursion; they do not assert that an arbitrary family of
objects is a family of heaps.  The combinatorial encoding is a separate bridge.
-/

namespace RootedKP

open scoped BigOperators

/-- Finite neighbourhoods, nonnegative activities and costs, and the KP inequality.
The numerical argument itself does not require symmetry or self-incompatibility.
Those belong to the heap model. -/
structure KPData (P : Type*) where
  neighbours : P → Finset P
  activity : P → ℝ
  cost : P → ℝ
  activity_nonneg : ∀ p, 0 ≤ activity p
  cost_nonneg : ∀ p, 0 ≤ cost p
  kp : ∀ p, ∑ q ∈ neighbours p, activity q * Real.exp (cost q) ≤ cost p

namespace KPData

variable {P : Type*} (K : KPData P)

/-- The proposed upper bound for the total mass at a specified root. -/
noncomputable def budget (p : P) : ℝ := K.activity p * Real.exp (K.cost p)

theorem budget_nonneg (p : P) : 0 ≤ K.budget p :=
  mul_nonneg (K.activity_nonneg p) (Real.exp_pos _).le

/-- One product-recursion step preserves the KP budget. -/
theorem product_le_budget (f : P → ℝ) (hf : ∀ p, 0 ≤ f p)
    (hbound : ∀ p, f p ≤ K.budget p) (p : P) :
    K.activity p * ∏ q ∈ K.neighbours p, (1 + f q) ≤ K.budget p := by
  calc
    K.activity p * ∏ q ∈ K.neighbours p, (1 + f q)
        ≤ K.activity p * Real.exp (∑ q ∈ K.neighbours p, f q) :=
      mul_le_mul_of_nonneg_left
        (Real.prod_one_add_le_exp_sum _ hf) (K.activity_nonneg p)
    _ ≤ K.activity p * Real.exp (K.cost p) := by
      apply mul_le_mul_of_nonneg_left _ (K.activity_nonneg p)
      apply Real.exp_le_exp.mpr
      exact (Finset.sum_le_sum (fun q _ => hbound q)).trans (K.kp p)
    _ = K.budget p := rfl

/-- Every finite-size truncation satisfying the heap product recursion obeys KP.
This is a conditional numerical theorem: the recursion must be proved from the
objects' encoding, rather than assumed to follow from the word "heap". -/
theorem mass_le_budget_of_product_recursion (mass : ℕ → P → ℝ)
    (hnonneg : ∀ n p, 0 ≤ mass n p)
    (hzero : ∀ p, mass 0 p = 0)
    (hstep : ∀ n p, mass (n + 1) p ≤
      K.activity p * ∏ q ∈ K.neighbours p, (1 + mass n q)) :
    ∀ n p, mass n p ≤ K.budget p := by
  intro n
  induction n with
  | zero =>
      intro p
      rw [hzero p]
      exact K.budget_nonneg p
  | succ n ih =>
      intro p
      exact (hstep n p).trans (K.product_le_budget (mass n) (hnonneg n) ih p)

end KPData
end RootedKP
