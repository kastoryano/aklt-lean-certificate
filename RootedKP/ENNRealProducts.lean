import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Option

/-! Product estimates for arbitrary nonnegative sums, without convergence hypotheses. -/

namespace RootedKP

open scoped BigOperators ENNReal

/-- A finite product of unrestricted nonnegative sums dominates the sum over
all independent choices, even before any of those sums is known to be finite. -/
theorem ennreal_tsum_pi_le {I : Type*} [Fintype I] {β : I → Type*}
    (f : ∀ i, β i → ℝ≥0∞) :
    (∑' g : ∀ i, β i, ∏ i, f i (g i)) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  let t : ∀ i, Finset (β i) := fun i => s.image (fun g => g i)
  have hsub : s ⊆ Fintype.piFinset t := by
    intro g hg
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  calc
    (∑ g ∈ s, ∏ i, f i (g i)) ≤ ∑ g ∈ Fintype.piFinset t, ∏ i, f i (g i) :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∏ i, ∑ x ∈ t i, f i x := (Finset.prod_univ_sum t f).symm
    _ ≤ ∏ i, ∑' x, f i x :=
      Finset.prod_le_prod (fun i _ => ENNReal.sum_le_tsum (t i))

/-- Choosing no heap has weight one; choosing a heap contributes its weight. -/
theorem ennreal_tsum_option {H : Type*} (w : H → ℝ≥0∞) :
    (∑' o : Option H, o.elim 1 w) = 1 + ∑' h, w h := by
  let e : Option H ≃ H ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit H
  calc
    (∑' o : Option H, o.elim 1 w) =
        ∑' s : H ⊕ PUnit.{1}, Sum.elim w (fun _ => 1) s := by
      convert e.tsum_eq (Sum.elim w (fun _ => (1 : ℝ≥0∞))) using 1
      apply tsum_congr
      intro o
      cases o <;> rfl
    _ = (∑' h, w h) + (∑' _ : PUnit.{1}, (1 : ℝ≥0∞)) :=
      Summable.tsum_sum ENNReal.summable ENNReal.summable
    _ = 1 + ∑' h, w h := by simp [add_comm]

end RootedKP
