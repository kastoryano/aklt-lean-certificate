import RootedKP.Target

/-!
# Assembly of the exact scalar conclusion

The two mathematical inputs in this file's assembly theorem are stated
explicitly. The concrete KP certificate and the uniform per-edge counting
estimate must discharge them; no missing input is a declared axiom.
-/

namespace RootedKP.AKLT

open scoped BigOperators ENNReal NNReal

theorem scalarSum_by_root (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut = ∑' p : Polymer F,
      (cutMarks cut Polymer.edges p : ℝ≥0∞) * fixedRootMass F p := by
  classical
  let f : RegionalRootedHeap F → ℝ≥0∞ := fun h =>
    (rootCutMarks F cut h : ℝ≥0∞) *
      (Heaps.Heap.weight Polymer.activity h.2.val : ℝ≥0)
  have hs : Function.support f ⊆ {h | 0 < rootCutMarks F cut h} := by
    intro h hh
    by_contra hn
    have hz : rootCutMarks F cut h = 0 := by
      change ¬ 0 < rootCutMarks F cut h at hn
      exact Nat.eq_zero_of_not_pos hn
    exact hh (by simp [f, hz])
  calc
    scalarSum F cut = ∑' h : RegionalRootedHeap F, f h := by
      exact tsum_subtype_eq_of_support_subset hs
    _ = ∑' p : Polymer F, ∑' h : Heaps.RootedHeap Polymer.Incompatible p,
        (cutMarks cut Polymer.edges p : ℝ≥0∞) *
          (Heaps.Heap.weight Polymer.activity h.val : ℝ≥0) :=
      ENNReal.tsum_sigma' f
    _ = ∑' p : Polymer F,
        (cutMarks cut Polymer.edges p : ℝ≥0∞) * fixedRootMass F p := by
      simp only [ENNReal.tsum_mul_left, fixedRootMass]

theorem scalarSum_count_marks (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut = ∑ e ∈ cut, ∑' p : Polymer F,
      if e ∈ p.edges then fixedRootMass F p else 0 := by
  classical
  rw [scalarSum_by_root]
  simp_rw [cutMarks_mul]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

/-- Precise assembly: fixed-root KP and a uniform finite root mass imply the
requested uniform scalar bound, including convergence. -/
theorem uniform_summability_of_two_bounds
    (hheap : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
      fixedRootMass F p ≤ rootBudget p)
    (hmass : UniformRootMass) : UniformRootedSummability := by
  classical
  obtain ⟨R, hR⟩ := hmass
  refine ⟨R, ?_⟩
  intro F cut
  rw [scalarSum_count_marks]
  calc
    (∑ e ∈ cut, ∑' p : Polymer F,
        if e ∈ p.edges then fixedRootMass F p else 0) ≤
        ∑ e ∈ cut, (R : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro e _
      exact (ENNReal.tsum_le_tsum (fun p => by
        split_ifs <;> simp_all)).trans (hR F e)
    _ = (cut.card : ℝ≥0∞) * R := by simp [nsmul_eq_mul]

end RootedKP.AKLT
