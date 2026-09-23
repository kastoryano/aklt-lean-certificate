import RootedKP.FiniteRegion
import RootedKP.ScalarAssembly
import RootedKP.HeapMass

/-!
# Application of abstract rooted KP to the literal AKLT polymers

The finite regional polymer alphabet needs no length cutoff. An arbitrary order
is used only inside the abstract heap proof. The two model-specific counting
conditions remain explicit hypotheses; this file does not prove either one.
-/

namespace RootedKP.AKLT

open scoped BigOperators ENNReal NNReal Classical

private theorem heap_weight_coe {P : Type*} {R : P → P → Prop}
    (w : P → ℝ≥0) (h : Heaps.Heap P R) :
    ((Heaps.Heap.weight w h : ℝ≥0) : ℝ≥0∞) =
      Heaps.Heap.weight (fun p => (w p : ℝ≥0∞)) h := by
  induction h using Quotient.inductionOn with
  | _ H =>
    letI := H.finite
    change ((∏ x, w (H.label x) : ℝ≥0) : ℝ≥0∞) =
      ∏ x, (w (H.label x) : ℝ≥0∞)
    simp only [ENNReal.ofNNReal_finsetProd]

/-- Convert the literal ENNReal KP condition to the finite real criterion used
by the abstract theorem. Symmetry reconciles the two argument orders. -/
theorem real_kp_of_uniform_kp (hKP : UniformKPCondition)
    (F : Honeycomb.Rectangle) (p : Polymer F) :
    ∑ q ∈ Finset.univ.filter (Polymer.Incompatible p),
      (q.activity : ℝ) * Real.exp q.cost ≤ p.cost := by
  classical
  apply (ENNReal.ofReal_le_ofReal_iff (Polymer.cost_nonneg p)).mp
  have h := hKP F p
  rw [tsum_fintype] at h
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ =>
    mul_nonneg q.activity.property (Real.exp_pos _).le)]
  simpa only [Finset.sum_filter, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal, Polymer.incompatible_symm p] using h

/-- The complete abstract heap proof applied to canonical, unoriented regional
polymers. The model-specific KP condition is the only remaining hypothesis. -/
theorem fixedRootMass_le_of_uniform_kp (hKP : UniformKPCondition)
    (F : Honeycomb.Rectangle) (p : Polymer F) :
    fixedRootMass F p ≤ rootBudget p := by
  classical
  letI : LinearOrder (Polymer F) :=
    LinearOrder.lift' (Fintype.equivFin (Polymer F)) (Fintype.equivFin _).injective
  have h := Heaps.rooted_heap_KP_of_criterion
    (P := Polymer F) Polymer.Incompatible (fun q => (q.activity : ℝ)) Polymer.cost
    (fun q => q.activity.property) Polymer.cost_nonneg Polymer.incompatible_self
    (real_kp_of_uniform_kp hKP F) p
  calc
    fixedRootMass F p = Heaps.rootedHeapMass
        (R := Polymer.Incompatible) (fun q => ENNReal.ofReal (q.activity : ℝ)) p := by
      apply tsum_congr
      intro H
      simpa only [ENNReal.ofReal_coe_nnreal] using heap_weight_coe Polymer.activity H.val
    _ ≤ rootBudget p := h

/-- Conditional model theorem: the literal KP and uniform per-edge root-counting
conditions imply the exact uniform rooted-heap summability target. -/
theorem uniform_rooted_summability_of_kp_and_root_mass
    (hKP : UniformKPCondition) (hmass : UniformRootMass) : UniformRootedSummability :=
  uniform_summability_of_two_bounds (fixedRootMass_le_of_uniform_kp hKP) hmass

end RootedKP.AKLT
