import RootedKP.Arithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite length fibres and cumulative count certificates

These lemmas relate actual finite sets to length counts and justify applying
the scalar certificate to cumulative upper counts.
-/

namespace RootedKP

open scoped BigOperators

theorem weighted_sum_by_length {P : Type*} [DecidableEq P]
    (s : Finset P) (length : P → ℕ) (w : ℕ → ℝ) (start count : ℕ)
    (hlen : ∀ p ∈ s, start ≤ length p ∧ length p < start + count) :
    (∑ p ∈ s, w (length p)) =
      ∑ i ∈ Finset.range count,
        ((s.filter fun p => length p = start + i).card : ℝ) * w (start + i) := by
  classical
  symm
  calc
    _ = ∑ i ∈ Finset.range count, ∑ p ∈ s,
        if length p = start + i then w (length p) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      calc
        _ = ∑ _p ∈ s.filter (fun p => length p = start + i), w (start + i) := by
          simp [nsmul_eq_mul]
        _ = _ := Finset.sum_congr rfl (by
          intro p hp
          rw [(Finset.mem_filter.mp hp).2])
    _ = ∑ p ∈ s, ∑ i ∈ Finset.range count,
        if length p = start + i then w (length p) else 0 := Finset.sum_comm
    _ = ∑ p ∈ s, w (length p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hl := hlen p hp
      rw [Finset.sum_eq_single (length p - start)]
      · rw [if_pos (by omega)]
      · intro i hi hne
        exact if_neg (by omega)
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))

theorem sumCounts_eq_sum_range (w : ℕ → ℚ) (start step : ℕ) (cs : List ℕ) :
    (Arithmetic.sumCounts w start step cs : ℝ) =
      ∑ i ∈ Finset.range cs.length, (cs[i]?.getD 0 : ℝ) * (w (start + step * i) : ℝ) := by
  induction cs generalizing start with
  | nil => simp [Arithmetic.sumCounts]
  | cons c cs ih =>
      rw [Arithmetic.sumCounts]
      push_cast
      rw [ih]
      simp only [List.length_cons, Finset.sum_range_succ']
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_cons_succ]
      conv_lhs => rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      ring

/-- Decreasing length weights may be combined with cumulative count bounds;
the supplied sequence need not bound every individual length. -/
theorem weighted_sum_le_of_cumulative_counts {P : Type*} [DecidableEq P]
    (s : Finset P) (length : P → ℕ) (start count : ℕ)
    (w : ℕ → ℝ) (upper : ℕ → ℝ)
    (hlen : ∀ p ∈ s, start ≤ length p ∧ length p < start + count)
    (hw : ∀ i < count, 0 ≤ w (start + i))
    (hdec : ∀ i, i + 1 < count → w (start + (i + 1)) ≤ w (start + i))
    (hcum : ∀ k ≤ count,
      Arithmetic.prefixSum
        (fun i => ((s.filter fun p => length p = start + i).card : ℝ)) k ≤
      Arithmetic.prefixSum upper k) :
    (∑ p ∈ s, w (length p)) ≤
      ∑ i ∈ Finset.range count, upper i * w (start + i) := by
  rw [weighted_sum_by_length s length w start count hlen]
  simpa only [mul_comm] using Arithmetic.cumulative_count_comparison
    (fun i => ((s.filter fun p => length p = start + i).card : ℝ)) upper
    (fun i => w (start + i)) count hw hdec hcum

end RootedKP
