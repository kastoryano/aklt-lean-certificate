import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases

/-!
# Exact rational arithmetic for the seven AKLT root classes

The parameters are μ = 1/500, long-root slope = 17/100, and
`c(n) = n + 6 * floor(n/4) - 7`.

The count lists below are INPUT DATA copied from the current Python certificate.
No theorem in this file asserts that these data cover honeycomb polymers.
The geometric coverage and counting bounds remain separate hypotheses.

We use slightly larger, compact rational envelopes instead of the Python
Taylor-24 fractions. The loop tail is also conservatively doubled, from 3/8
to 3/4, to use the proved elementary count bound 2^(n-2) instead of 2^(n-3).
Only the verified finite loop prefix through length 20 is used; the tail starts
at length 22. The unused suffix of `loopCounts` is retained as source data only.
Their exponential validity is proved below using mathlib's
Taylor remainder theorem. Every displayed ratio inequality is checked by the
Lean kernel; neither `native_decide` nor additional axioms are used.
-/

namespace RootedKP.Arithmetic

open scoped BigOperators

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def mu : ℚ := 1 / 500
def slope : ℚ := 17 / 100
def pathFactor : ℚ := 5 / 6

def a (n : ℕ) : ℚ :=
  match n with
  | 3 => 52 / 100
  | 4 => 56 / 100
  | 5 => 66 / 100
  | 6 => 70 / 100
  | _ => slope * n

/-- The Python Taylor-24 formula, retained to document the exact convention. -/
def taylor24Upper (x : ℚ) : ℚ :=
  (∑ k ∈ Finset.range 25, x ^ k / (Nat.factorial k : ℚ)) +
    (x ^ 25 / (Nat.factorial 25 : ℚ)) / (1 - x / 26)

/-- A compact, conservative upper bound for exp(17/100+1/500)/3. -/
def rCap : ℚ := 99 / 250
def qCap : ℚ := 2 * rCap

def weightCap (n : ℕ) : ℚ :=
  match n with
  | 3 => 189 / 1000
  | 4 => 66 / 1000
  | 5 => 25 / 1000
  | 6 => 9 / 1000
  | _ => 3 * rCap ^ n

def W3Counts : List ℕ :=
  [1,2,2,2,6,8,14,18,38,52,106,150,296,428,868,1284,2530,3818]
def W4Counts : List ℕ :=
  [1,2,2,2,7,9,18,22,50,70,140,224,404,655,1207,2084,3525,6504]
def W5Counts : List ℕ :=
  [1,3,2,3,7,12,19,27,55,78,156,225,454,644,1337,1940,3985,5793]
def W6Counts : List ℕ :=
  [1,3,2,3,7,13,20,30,62,91,179,286,511,874,1561,2727,4776,8478]
def L6Counts : List ℕ :=
  [1,2,2,2,7,10,20,24,60,70,174,221,547,641,1800,1980,5640,6078]
def loopCounts : List ℕ := [2,0,10,8,56,96,390,920,3168,8592,28002,81368]
def evenCountsFrom8 : List ℕ := [4,9,26,75,215,649,1943]
def oddCounts : List ℕ := [1,2,7,20,64,202,647,2094,6803]

def sumCounts (f : ℕ → ℚ) (n step : ℕ) : List ℕ → ℚ
  | [] => 0
  | c :: cs => (c : ℚ) * f n + sumCounts f (n + step) step cs

def tail0 : ℚ := qCap ^ 21 / (1 - qCap)
def tail1 : ℚ := qCap ^ 21 * (21 / (1 - qCap) + qCap / (1 - qCap) ^ 2)
def interiorTail : ℚ := (3 / 1024) * (2 * tail1 + 95 * tail0)
def boundaryTail : ℚ := (3 / 16) * tail0
def loopMass : ℚ := sumCounts weightCap 6 2 (loopCounts.take 8) +
  (3 / 4) * qCap ^ 22 / (1 - qCap * qCap)

def shortPathRatio (ell : ℕ) (counts : List ℕ) : ℚ :=
  (pathFactor * (sumCounts weightCap 3 1 counts + boundaryTail +
    ((ell : ℚ) - 2) * interiorTail) + ((ell : ℚ) - 2) * loopMass) / a ell

def shortLoopRatio : ℚ :=
  (pathFactor * (sumCounts weightCap 3 1 L6Counts + 6 * interiorTail) +
    6 * loopMass) / a 6

def collarCoefficient (n : ℕ) : ℚ := (n : ℚ) + 6 * (n / 4 : ℕ) - 7

def longRatio (j : ℕ) : ℚ :=
  (pathFactor * ((1 / 2 + 1 / (j : ℚ)) * weightCap 4 + 2 * weightCap 6 +
      sumCounts (fun n => (1 / 2 + collarCoefficient n / (j : ℚ)) *
        weightCap n) 8 2 evenCountsFrom8 +
      sumCounts (fun n => weightCap n / (j : ℚ)) 3 2 oddCounts + interiorTail) +
    loopMass) / slope

theorem qCap_interval : 0 < qCap ∧ qCap < 1 := by
  norm_num [qCap, rCap]

theorem weightCap_nonneg (n : ℕ) : 0 ≤ weightCap n := by
  unfold weightCap rCap
  split <;> positivity

theorem weightCap_eq_long (n : ℕ) (hn : 7 ≤ n) : weightCap n = 3 * rCap ^ n := by
  unfold weightCap
  split <;> first | rfl | omega

/-- Decreasing envelopes justify using successive differences of cumulative counts. -/
theorem weightCap_decreasing (n : ℕ) (hn : 3 ≤ n) : weightCap (n + 1) ≤ weightCap n := by
  by_cases hsmall : n < 7
  · interval_cases n <;> norm_num [weightCap, rCap]
  · have hlarge : 7 ≤ n := by omega
    rw [weightCap_eq_long (n + 1) (by omega), weightCap_eq_long n hlarge, pow_succ]
    have hr : rCap ≤ 1 := by norm_num [rCap]
    have hp : 0 ≤ 3 * rCap ^ n := by unfold rCap; positivity
    calc
      3 * (rCap ^ n * rCap) = (3 * rCap ^ n) * rCap := by ring
      _ ≤ (3 * rCap ^ n) * 1 := mul_le_mul_of_nonneg_left hr hp
      _ = 3 * rCap ^ n := by ring

/-- The original Taylor-24 numerical certificate is dominated by our envelope. -/
theorem taylor24_slope_bound : taylor24Upper (43 / 250) / 3 ≤ rCap := by
  norm_num [taylor24Upper, Finset.sum_range_succ, Nat.factorial, rCap]

theorem taylor24_weight3_bound : taylor24Upper (263 / 500) / 9 ≤ weightCap 3 := by
  norm_num [taylor24Upper, Finset.sum_range_succ, Nat.factorial, weightCap]

theorem taylor24_weight4_bound : taylor24Upper (71 / 125) / 27 ≤ weightCap 4 := by
  norm_num [taylor24Upper, Finset.sum_range_succ, Nat.factorial, weightCap]

theorem taylor24_weight5_bound : taylor24Upper (67 / 100) / 81 ≤ weightCap 5 := by
  norm_num [taylor24Upper, Finset.sum_range_succ, Nat.factorial, weightCap]

theorem taylor24_weight6_bound : taylor24Upper (89 / 125) / 243 ≤ weightCap 6 := by
  norm_num [taylor24Upper, Finset.sum_range_succ, Nat.factorial, weightCap]

theorem W3_ratio : shortPathRatio 3 W3Counts < 834 / 1000 := by
  norm_num [shortPathRatio, W3Counts, sumCounts, weightCap, rCap, qCap,
    pathFactor, boundaryTail, interiorTail, tail0, tail1, loopMass, loopCounts, a]

theorem W4_ratio : shortPathRatio 4 W4Counts < 879 / 1000 := by
  norm_num [shortPathRatio, W4Counts, sumCounts, weightCap, rCap, qCap,
    pathFactor, boundaryTail, interiorTail, tail0, tail1, loopMass, loopCounts, a]

theorem W5_ratio : shortPathRatio 5 W5Counts < 922 / 1000 := by
  norm_num [shortPathRatio, W5Counts, sumCounts, weightCap, rCap, qCap,
    pathFactor, boundaryTail, interiorTail, tail0, tail1, loopMass, loopCounts, a]

theorem W6_ratio : shortPathRatio 6 W6Counts < 944 / 1000 := by
  norm_num [shortPathRatio, W6Counts, sumCounts, weightCap, rCap, qCap,
    pathFactor, boundaryTail, interiorTail, tail0, tail1, loopMass, loopCounts, a]

theorem L6_ratio : shortLoopRatio < 968 / 1000 := by
  norm_num [shortLoopRatio, L6Counts, sumCounts, weightCap, rCap, qCap,
    pathFactor, interiorTail, tail0, tail1, loopMass, loopCounts, a]

theorem long_path_ratio : longRatio 7 < 939 / 1000 := by
  norm_num [longRatio, sumCounts, weightCap, rCap, qCap, pathFactor, slope,
    collarCoefficient, evenCountsFrom8, oddCounts, interiorTail,
    tail0, tail1, loopMass, loopCounts]

theorem long_loop_ratio : longRatio 10 < 823 / 1000 := by
  norm_num [longRatio, sumCounts, weightCap, rCap, qCap, pathFactor, slope,
    collarCoefficient, evenCountsFrom8, oddCounts, interiorTail,
    tail0, tail1, loopMass, loopCounts]

/-- Seven strict KP arithmetic margins, conditional on the count interpretations. -/
theorem all_seven_below_one :
    shortPathRatio 3 W3Counts < 1 ∧ shortPathRatio 4 W4Counts < 1 ∧
    shortPathRatio 5 W5Counts < 1 ∧ shortPathRatio 6 W6Counts < 1 ∧
    shortLoopRatio < 1 ∧ longRatio 7 < 1 ∧ longRatio 10 < 1 := by
  have h3 := W3_ratio
  have h4 := W4_ratio
  have h5 := W5_ratio
  have h6 := W6_ratio
  have hl := L6_ratio
  have hp := long_path_ratio
  have hq := long_loop_ratio
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The analytic Taylor remainder supplied by mathlib, specialized to order 8. -/
theorem exp_le_taylor8 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ (∑ k ∈ Finset.range 8, x ^ k / (Nat.factorial k : ℝ)) +
      x ^ 8 * 9 / ((Nat.factorial 8 : ℝ) * 8) := by
  convert Real.exp_bound' hx0 hx1 (by norm_num : 0 < (8 : ℕ)) using 1
  norm_num

theorem exp_slope_bound : Real.exp (43 / 250 : ℝ) / 3 ≤ (rCap : ℝ) := by
  have h := exp_le_taylor8 (43 / 250) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [rCap]
  linarith

theorem exp_weight3_bound : Real.exp (263 / 500 : ℝ) / 9 ≤
    (weightCap 3 : ℝ) := by
  have h := exp_le_taylor8 (263 / 500) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [weightCap]
  linarith

theorem exp_weight4_bound : Real.exp (71 / 125 : ℝ) / 27 ≤
    (weightCap 4 : ℝ) := by
  have h := exp_le_taylor8 (71 / 125) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [weightCap]
  linarith

theorem exp_weight5_bound : Real.exp (67 / 100 : ℝ) / 81 ≤
    (weightCap 5 : ℝ) := by
  have h := exp_le_taylor8 (67 / 100) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [weightCap]
  linarith

theorem exp_weight6_bound : Real.exp (89 / 125 : ℝ) / 243 ≤
    (weightCap 6 : ℝ) := by
  have h := exp_le_taylor8 (89 / 125) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  norm_num [weightCap]
  linarith

/-- All long-length exponential weights are bounded, not just finitely many. -/
theorem long_weight_bound (n : ℕ) :
    3 * Real.exp ((n : ℝ) * (43 / 250)) / 3 ^ n ≤
      3 * (rCap : ℝ) ^ n := by
  rw [Real.exp_nat_mul]
  calc
    3 * Real.exp (43 / 250) ^ n / 3 ^ n =
        3 * (Real.exp (43 / 250) / 3) ^ n := by rw [div_pow]; ring
    _ ≤ 3 * (rCap : ℝ) ^ n := by
      gcongr
      exact exp_slope_bound

/-- The actual exponential activity weight, before replacing it by a rational envelope. -/
noncomputable def analyticWeight (n : ℕ) : ℝ :=
  3 * Real.exp ((a n + mu * n : ℚ) : ℝ) / 3 ^ n

theorem analyticWeight_nonneg (n : ℕ) : 0 ≤ analyticWeight n := by
  unfold analyticWeight
  positivity

theorem analyticWeight_le (n : ℕ) (hn : 3 ≤ n) :
    analyticWeight n ≤ (weightCap n : ℝ) := by
  by_cases hsmall : n < 7
  · interval_cases n
    · have h := exp_weight3_bound
      norm_num [analyticWeight, a, mu] at *
      linarith
    · have h := exp_weight4_bound
      norm_num [analyticWeight, a, mu] at *
      linarith
    · have h := exp_weight5_bound
      norm_num [analyticWeight, a, mu] at *
      linarith
    · have h := exp_weight6_bound
      norm_num [analyticWeight, a, mu] at *
      linarith
  · have hn7 : 7 ≤ n := by omega
    have ha : a n = slope * n := by
      unfold a
      split <;> first | rfl | omega
    have he : ((slope * (n : ℚ) + mu * n : ℚ) : ℝ) =
        (n : ℝ) * (43 / 250) := by
      norm_num [slope, mu]
      ring
    rw [analyticWeight, ha, he, weightCap_eq_long n hn7]
    push_cast
    exact long_weight_bound n

/-- Exact value of the infinite geometric tail used in `tail0`. -/
theorem geometric_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun k : ℕ => q ^ (m + k)) (q ^ m / (1 - q)) := by
  simpa only [pow_add, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left (q ^ m)

/-- Exact first-moment tail used in `tail1`. -/
theorem first_moment_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun k : ℕ => ((m + k : ℕ) : ℝ) * q ^ (m + k))
      (q ^ m * ((m : ℝ) / (1 - q) + q / (1 - q) ^ 2)) := by
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have hn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one hn
  convert ((hg.mul_left (m : ℝ)).add hm).mul_left (q ^ m) using 1
  · funext k
    rw [Nat.cast_add, pow_add]
    ring
  · ring

/-- Exact even-length loop tail beginning at any chosen length. -/
theorem even_loop_tail (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun k : ℕ => q ^ (m + 2 * k)) (q ^ m / (1 - q ^ 2)) := by
  have hsq0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hsq1 : q ^ 2 < 1 := by nlinarith
  simpa only [pow_add, pow_mul, div_eq_mul_inv] using
    (hasSum_geometric_of_lt_one hsq0 hsq1).mul_left (q ^ m)

def prefixSum (c : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, c i

theorem prefixSum_succ (c : ℕ → ℝ) (n : ℕ) :
    prefixSum c (n + 1) = prefixSum c n + c n := by
  simp only [prefixSum, Finset.sum_range_succ]

/-- Finite Abel summation, with an explicit final cumulative term. -/
theorem abel_identity (c w : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), w i * c i) =
      w n * prefixSum c (n + 1) +
        ∑ i ∈ Finset.range n, (w i - w (i + 1)) * prefixSum c (i + 1) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [Finset.sum_range_succ (f := fun i => w i * c i), ih,
      Finset.sum_range_succ (f := fun i => (w i - w (i + 1)) * prefixSum c (i + 1)),
      prefixSum_succ c (n + 1)]
    ring

/--
Cumulative-count domination suffices for decreasing nonnegative weights.
The sequences themselves need not be nonnegative, so this includes the requested
nonnegative-count case without an unnecessary hypothesis.
-/
theorem cumulative_count_comparison (c d w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i < n, 0 ≤ w i)
    (hdec : ∀ i, i + 1 < n → w (i + 1) ≤ w i)
    (hprefix : ∀ k ≤ n, prefixSum c k ≤ prefixSum d k) :
    (∑ i ∈ Finset.range n, w i * c i) ≤ ∑ i ∈ Finset.range n, w i * d i := by
  cases n with
  | zero => simp
  | succ n =>
    rw [abel_identity, abel_identity]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (hprefix (n + 1) le_rfl) (hw n (by omega))
    · apply Finset.sum_le_sum
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_left (hprefix (i + 1) (by omega))
        (sub_nonneg.mpr (hdec i (by omega)))

end RootedKP.Arithmetic

#print axioms RootedKP.Arithmetic.all_seven_below_one
#print axioms RootedKP.Arithmetic.long_weight_bound
#print axioms RootedKP.Arithmetic.first_moment_tail
#print axioms RootedKP.Arithmetic.cumulative_count_comparison

#print axioms RootedKP.Arithmetic.analyticWeight_le
