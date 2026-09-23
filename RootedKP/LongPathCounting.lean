import RootedKP.PathTails

/-!
# Explicit unweighted long-root count interface

The allowances pay proportionally for multiple widely separated corners:
the odd-path count is bounded by (root length / 7) times the corner table.
No single-corner assumption is made about an arbitrary long root.
-/

namespace RootedKP.AKLT

open scoped BigOperators Classical
open Arithmetic

def longCountCoefficient (n : ℕ) : ℚ :=
  if n = 4 then 1 / 2 + 1 / 7
  else if n = 6 then 2
  else if n % 2 = 1 then (oddCounts[(n - 3) / 2]?.getD 0 : ℚ) / 7
  else (1 / 2 + collarCoefficient n / 7) *
    (evenCountsFrom8[(n - 8) / 2]?.getD 0 : ℚ)

theorem long_coefficient_identity :
    (∑ i ∈ Finset.range 18, longCountCoefficient (3 + i) * weightCap (3 + i)) =
      longFinitePathAllowance 7 / 7 := by
  norm_num [Finset.sum_range_succ, longCountCoefficient, longFinitePathAllowance,
    sumCounts, evenCountsFrom8, oddCounts, collarCoefficient, weightCap, rCap]

def LongLengthCountBound : Prop := ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
  7 ≤ p.length → ∀ i < 18,
    (pathLengthCount p i : ℝ) ≤ (p.length : ℝ) * (longCountCoefficient (3 + i) : ℝ)

theorem long_envelope_of_length_counts (H : LongLengthCountBound)
    (F : Honeycomb.Rectangle) (p : Polymer F) (hp : 7 ≤ p.length) :
    shortPathEnvelope p ≤ (longFiniteUniformAllowance p.length : ℝ) := by
  classical
  have hlen : ∀ q ∈ shortPathSet p, 3 ≤ q.length ∧ q.length < 3 + 18 := by
    intro q hq
    have hh := (Finset.mem_filter.mp hq).2
    exact ⟨q.length_ge_three, by omega⟩
  calc
    shortPathEnvelope p = ∑ i ∈ Finset.range 18,
        (pathLengthCount p i : ℝ) * (weightCap (3 + i) : ℝ) :=
      weighted_sum_by_length (shortPathSet p) Polymer.length
        (fun n => (weightCap n : ℝ)) 3 18 hlen
    _ ≤ ∑ i ∈ Finset.range 18,
        ((p.length : ℝ) * (longCountCoefficient (3 + i) : ℝ)) *
          (weightCap (3 + i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right (H F p hp i (Finset.mem_range.mp hi))
      exact_mod_cast weightCap_nonneg (3 + i)
    _ = (p.length : ℝ) *
        ((∑ i ∈ Finset.range 18, longCountCoefficient (3 + i) * weightCap (3 + i) : ℚ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (longFiniteUniformAllowance p.length : ℝ) := by
      rw [long_coefficient_identity]
      simp only [longFiniteUniformAllowance, Rat.cast_mul, Rat.cast_natCast]

/-- The remaining input consists entirely of actual unweighted path counts.
The loop bounds, activity comparisons, sums, and scalar margins are proved. -/
structure UnweightedPathCountingInputs : Prop where
  shortRoots : ∀ (F : Honeycomb.Rectangle) (p : Polymer F), p.length ≤ 6 →
    CumulativePathBound p (if p.kind = .path then shortCounts p.length else L6Counts)
  longRoots : LongLengthCountBound
  tails : TailLengthCountBound

theorem weighted_inputs_of_unweighted (H : UnweightedPathCountingInputs) :
    PathCountingInputs :=
  pathCountingInputs_of_counts H.shortRoots (long_envelope_of_length_counts H.longRoots) H.tails

end RootedKP.AKLT
