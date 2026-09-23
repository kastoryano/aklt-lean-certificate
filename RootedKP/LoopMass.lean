import RootedKP.RegionalLoopCounting
import RootedKP.KPAccounting

namespace RootedKP.AKLT
open Honeycomb
open scoped BigOperators
set_option maxHeartbeats 0

/-- Charge each incompatible canonical loop to an edge in a finite root cover.
Multiple charges only enlarge the sum because the weights are nonnegative. -/
theorem loop_mass_le_edge_cover {F : Rectangle} (p : Polymer F) (C : Finset Edge)
    (hcover : ∀ q : Polymer F, q.kind = .loop → Polymer.Incompatible q p →
      ∃ edge ∈ C, edge ∈ q.edges) :
    kindMass p .loop ≤ (C.card : ℝ) * (Arithmetic.loopMass : ℝ) := by
  classical
  unfold kindMass
  calc
    _ ≤ ∑ q ∈ kindSet p .loop, ∑ edge ∈ C,
        if edge ∈ q.edges then realBudget q else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      obtain ⟨edge,hedge,hmem⟩ := hcover q hq'.1 hq'.2
      have h := Finset.single_le_sum (s := C)
        (f := fun edge => if edge ∈ q.edges then realBudget q else 0)
        (fun edge _ => by split_ifs <;> first | exact realBudget_nonneg q | exact le_rfl) hedge
      simpa only [if_pos hmem] using h
    _ = ∑ edge ∈ C, ∑ q ∈ kindSet p .loop,
        if edge ∈ q.edges then realBudget q else 0 := Finset.sum_comm
    _ ≤ ∑ edge ∈ C, ∑ q ∈ loopEdgeSet F edge, realBudget q := by
      apply Finset.sum_le_sum
      intro edge _
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        have hf := Finset.mem_filter.mp hq
        have hk := (Finset.mem_filter.mp hf.1).2.1
        simp only [loopEdgeSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hk,hf.2⟩
      · intro q _ _
        exact realBudget_nonneg q
    _ ≤ ∑ _edge ∈ C, (Arithmetic.loopMass : ℝ) := by
      apply Finset.sum_le_sum
      intro edge _
      exact loop_edge_mass_le F edge
    _ = _ := by simp

end RootedKP.AKLT
#print axioms RootedKP.AKLT.loop_mass_le_edge_cover
