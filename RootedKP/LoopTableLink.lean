import RootedKP.Arithmetic
import RootedKP.LoopCountsTable

/-!
This theorem ties the already kernel-counted loop prefix to the exact list used
by the rational certificate. Only these eight entries are used by the arithmetic certificate. A proved
all-length count bound controls the complete remaining even-length tail.
-/

namespace RootedKP.LoopCounts

open Honeycomb Enumeration
open scoped BigOperators

set_option maxHeartbeats 0

/-- The all-length bound used by the conservative `3/4` loop tail. -/
theorem anchoredLoops_card_le (n : ℕ) : (anchoredLoops n).card ≤ 2 ^ (n - 2) := by
  have hs : ∀ u v, v ∈ neighbors u → u ∈ neighbors v := by
    intro u v hv
    exact (mem_neighbors v u).mpr (adj_symm ((mem_neighbors u v).mp hv))
  have hc := card_extensions_after_edge_le neighbors hs
    (fun u => (neighbors_card u).le) (n - 2) first origin []
    (by simp [first, origin, neighbors])
  exact (Finset.card_filter_le _ _).trans hc

theorem loop_input_prefix :
    [(anchoredLoops 6).card, (anchoredLoops 8).card, (anchoredLoops 10).card,
      (anchoredLoops 12).card, (anchoredLoops 14).card, (anchoredLoops 16).card,
      (anchoredLoops 18).card, (anchoredLoops 20).card] =
      Arithmetic.loopCounts.take 8 := by
  rw [loops6, loops8, loops10, loops12, loops14, loops16, loops18, loops20]
  rfl

/-- The complete even-loop series with the certified rational weight envelope. -/
def anchoredEvenTerm (k : ℕ) : ℝ :=
  ((anchoredLoops (6 + 2 * k)).card : ℝ) *
    (Arithmetic.weightCap (6 + 2 * k) : ℝ)

theorem anchored_weight_le (n : ℕ) (hn : 7 ≤ n) :
    ((anchoredLoops n).card : ℚ) * Arithmetic.weightCap n ≤
      (3 / 4) * Arithmetic.qCap ^ n := by
  have hc : ((anchoredLoops n).card : ℚ) ≤ (2 : ℚ) ^ (n - 2) := by
    exact_mod_cast anchoredLoops_card_le n
  have hp (m : ℕ) : (2 : ℚ) ^ m * (3 * Arithmetic.rCap ^ (m + 2)) =
      (3 / 4) * Arithmetic.qCap ^ (m + 2) := by
    simp only [Arithmetic.qCap, pow_add, mul_pow]
    ring
  calc
    _ ≤ (2 : ℚ) ^ (n - 2) * (3 * Arithmetic.rCap ^ n) := by
      rw [Arithmetic.weightCap_eq_long n hn]
      exact mul_le_mul_of_nonneg_right hc (by unfold Arithmetic.rCap; positivity)
    _ = _ := by simpa only [Nat.sub_add_cancel (by omega : 2 ≤ n)] using hp (n - 2)

theorem anchoredEvenTerm_nonneg (k : ℕ) : 0 ≤ anchoredEvenTerm k := by
  have h : (0 : ℝ) ≤ (Arithmetic.weightCap (6 + 2 * k) : ℝ) := by
    exact_mod_cast Arithmetic.weightCap_nonneg (6 + 2 * k)
  unfold anchoredEvenTerm
  positivity

theorem anchoredEvenTerm_tail_le (k : ℕ) :
    anchoredEvenTerm (k + 8) ≤
      (3 / 4 : ℝ) * (Arithmetic.qCap : ℝ) ^ (22 + 2 * k) := by
  have he : 6 + 2 * (k + 8) = 22 + 2 * k := by omega
  unfold anchoredEvenTerm
  rw [he]
  have h := (Rat.cast_le (K := ℝ)).mpr (anchored_weight_le (22 + 2 * k) (by omega))
  push_cast at h
  exact h

theorem anchoredEvenTail_hasSum :
    HasSum (fun k : ℕ => (3 / 4 : ℝ) * (Arithmetic.qCap : ℝ) ^ (22 + 2 * k))
      ((3 / 4 : ℝ) * (Arithmetic.qCap : ℝ) ^ 22 /
        (1 - (Arithmetic.qCap : ℝ) ^ 2)) := by
  have hq0 : (0 : ℝ) ≤ (Arithmetic.qCap : ℝ) := by
    norm_num [Arithmetic.qCap, Arithmetic.rCap]
  have hq1 : (Arithmetic.qCap : ℝ) < 1 := by
    norm_num [Arithmetic.qCap, Arithmetic.rCap]
  convert (Arithmetic.even_loop_tail _ hq0 hq1 22).mul_left (3 / 4 : ℝ) using 1; ring

theorem anchoredEvenTerm_summable : Summable anchoredEvenTerm := by
  apply (summable_nat_add_iff 8).mp
  exact Summable.of_nonneg_of_le (fun k => anchoredEvenTerm_nonneg (k + 8))
    anchoredEvenTerm_tail_le anchoredEvenTail_hasSum.summable

theorem anchoredEven_prefix :
    (∑ k ∈ Finset.range 8, anchoredEvenTerm k) =
      (Arithmetic.sumCounts Arithmetic.weightCap 6 2
        (Arithmetic.loopCounts.take 8) : ℝ) := by
  norm_num [Finset.sum_range_succ, anchoredEvenTerm, loops6, loops8, loops10,
    loops12, loops14, loops16, loops18, loops20, Arithmetic.loopCounts,
    Arithmetic.sumCounts, Arithmetic.weightCap, Arithmetic.rCap]

/-- No unverified finite loop counts occur in this complete infinite mass bound. -/
theorem anchoredEvenMass_le :
    (∑' k : ℕ, anchoredEvenTerm k) ≤ (Arithmetic.loopMass : ℝ) := by
  rw [← anchoredEvenTerm_summable.sum_add_tsum_nat_add 8, anchoredEven_prefix]
  have hs := (Summable.of_nonneg_of_le
    (fun k => anchoredEvenTerm_nonneg (k + 8)) anchoredEvenTerm_tail_le
    anchoredEvenTail_hasSum.summable).tsum_le_tsum
      anchoredEvenTerm_tail_le anchoredEvenTail_hasSum.summable
  rw [anchoredEvenTail_hasSum.tsum_eq] at hs
  calc
    _ ≤ (Arithmetic.sumCounts Arithmetic.weightCap 6 2
        (Arithmetic.loopCounts.take 8) : ℝ) +
        (3 / 4 : ℝ) * (Arithmetic.qCap : ℝ) ^ 22 /
          (1 - (Arithmetic.qCap : ℝ) ^ 2) := add_le_add le_rfl hs
    _ = _ := by push_cast [Arithmetic.loopMass]; ring

/-- The same complete loop bound for the actual exponential activity weights. -/
theorem anchoredEvenAnalyticMass_le :
    (∑' k : ℕ, ((anchoredLoops (6 + 2 * k)).card : ℝ) *
      Arithmetic.analyticWeight (6 + 2 * k)) ≤ (Arithmetic.loopMass : ℝ) := by
  have hp (k : ℕ) : ((anchoredLoops (6 + 2 * k)).card : ℝ) *
      Arithmetic.analyticWeight (6 + 2 * k) ≤ anchoredEvenTerm k := by
    exact mul_le_mul_of_nonneg_left (Arithmetic.analyticWeight_le _ (by omega))
      (Nat.cast_nonneg _)
  have hn (k : ℕ) : (0 : ℝ) ≤ ((anchoredLoops (6 + 2 * k)).card : ℝ) *
      Arithmetic.analyticWeight (6 + 2 * k) :=
    mul_nonneg (Nat.cast_nonneg _) (Arithmetic.analyticWeight_nonneg _)
  exact ((Summable.of_nonneg_of_le hn hp anchoredEvenTerm_summable).tsum_le_tsum
    hp anchoredEvenTerm_summable).trans anchoredEvenMass_le

end RootedKP.LoopCounts

#print axioms RootedKP.LoopCounts.loop_input_prefix
#print axioms RootedKP.LoopCounts.anchoredLoops_card_le

#print axioms RootedKP.LoopCounts.anchoredEvenMass_le

#print axioms RootedKP.LoopCounts.anchoredEvenAnalyticMass_le
