import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Counting cut marks and convergence

These are general counting identities. They do not assume convergence: all
initial sums take values in the extended nonnegative reals. The last theorem
deduces ordinary real summability from a finite bound.

`H` may be the type of all rooted heaps, `P` the polymer type, and `root` the
root label. This module does not assume that arbitrary `H` is a heap type.
Applying it to the paper requires the separate heap and AKLT geometry modules.
-/

namespace RootedKP

open scoped BigOperators ENNReal NNReal

variable {H P E : Type*} [DecidableEq E]

/-- Sum over objects with prescribed root label, including infinitely many objects. -/
noncomputable def rootedMass (root : H → P) (w : H → ℝ≥0∞) (p : P) : ℝ≥0∞ :=
  ∑' h : {h : H // root h = p}, w h

/-- Number of edges in the finite cut that belong to a root polymer. -/
noncomputable def cutMarks (C : Finset E) (support : P → Finset E) (p : P) : ℕ :=
  by classical exact (C.filter (fun e => e ∈ support p)).card

theorem weighted_root_regroup (root : H → P) (w : H → ℝ≥0∞) (c : P → ℝ≥0∞) :
    (∑' h, c (root h) * w h) = ∑' p, c p * rootedMass root w p := by
  classical
  calc
    (∑' h, c (root h) * w h) =
        ∑' p, ∑' h : {h : H // root h = p}, c (root h) * w h :=
      (ENNReal.tsum_fiberwise (fun h => c (root h) * w h) root).symm
    _ = ∑' p, c p * rootedMass root w p := by
      apply tsum_congr
      intro p
      rw [rootedMass, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro h
      rw [h.property]

theorem cutMarks_mul (C : Finset E) (support : P → Finset E)
    (p : P) (x : ℝ≥0∞) :
    (cutMarks C support p : ℝ≥0∞) * x =
      ∑ e ∈ C, if e ∈ support p then x else 0 := by
  classical
  simp [cutMarks, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]

/-- The cut-mark identity, valid before convergence has been established. -/
theorem count_cut_marks (C : Finset E) (support : P → Finset E)
    (root : H → P) (w : H → ℝ≥0∞) :
    (∑' h, (cutMarks C support (root h) : ℝ≥0∞) * w h) =
      ∑ e ∈ C, ∑' p, if e ∈ support p then rootedMass root w p else 0 := by
  classical
  rw [weighted_root_regroup root w (fun p => (cutMarks C support p : ℝ≥0∞))]
  simp_rw [cutMarks_mul]
  exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

/-- Conditional assembly of fixed-root bounds and per-edge root counting.
The hypotheses are explicit: this theorem alone is not the AKLT certificate. -/
theorem cut_mass_le (C : Finset E) (support : P → Finset E)
    (root : H → P) (w : H → ℝ≥0∞) (b : P → ℝ≥0∞) (R : ℝ≥0∞)
    (hroot : ∀ p, rootedMass root w p ≤ b p)
    (hedge : ∀ e ∈ C, (∑' p, if e ∈ support p then b p else 0) ≤ R) :
    (∑' h, (cutMarks C support (root h) : ℝ≥0∞) * w h) ≤ C.card * R := by
  classical
  rw [count_cut_marks]
  calc
    (∑ e ∈ C, ∑' p, if e ∈ support p then rootedMass root w p else 0) ≤
        ∑ e ∈ C, R := by
      apply Finset.sum_le_sum
      intro e he
      exact (ENNReal.tsum_le_tsum (fun p => by
        split_ifs <;> simp_all)).trans (hedge e he)
    _ = C.card * R := by simp [nsmul_eq_mul]

/-- A finite uniform root-mass bound proves convergence of the marked heap sum. -/
theorem cut_mass_summable (C : Finset E) (support : P → Finset E)
    (root : H → P) (w : H → ℝ≥0) (b : P → ℝ≥0∞) (R : ℝ≥0)
    (hroot : ∀ p, rootedMass root (fun h => (w h : ℝ≥0∞)) p ≤ b p)
    (hedge : ∀ e ∈ C, (∑' p, if e ∈ support p then b p else 0) ≤ (R : ℝ≥0∞)) :
    Summable (fun h => (cutMarks C support (root h) : ℝ) * (w h : ℝ)) := by
  have hbound := cut_mass_le C support root (fun h => (w h : ℝ≥0∞)) b R hroot hedge
  have hfinite : (∑' h, (cutMarks C support (root h) : ℝ≥0∞) * (w h : ℝ≥0∞)) ≠ ∞ :=
    ne_top_of_le_ne_top (by finiteness) hbound
  have hs := (ENNReal.tsum_coe_ne_top_iff_summable_coe
    (f := fun h => (cutMarks C support (root h) : ℝ≥0) * w h)).mp
      (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using hfinite)
  simpa using hs

/-- The analytic root-counting tail: a linear prefactor times a geometric
sequence is summable. The combinatorial counting bound is a separate input. -/
theorem summable_linear_geometric {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (n : ℝ) * q ^ n) := by
  exact (hasSum_coe_mul_geometric_of_norm_lt_one
    (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).summable

/-- A bound on each length fibre gives an explicit finite bound for all roots.
This isolates the elementary analytic part from the graph-counting input. -/
theorem root_mass_le_of_length_bounds (length : P → ℕ) (b : P → ℝ≥0∞)
    {C q : ℝ} (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcount : ∀ n, (∑' p : {p : P // length p = n}, b p) ≤
      ENNReal.ofReal (C * ((n : ℝ) * q ^ n))) :
    (∑' p, b p) ≤ ENNReal.ofReal (C * (q / (1 - q) ^ 2)) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left C
  calc
    (∑' p, b p) = ∑' n, ∑' p : {p : P // length p = n}, b p :=
      (ENNReal.tsum_fiberwise b length).symm
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * ((n : ℝ) * q ^ n)) :=
      ENNReal.tsum_le_tsum hcount
    _ = ENNReal.ofReal (∑' n : ℕ, C * ((n : ℝ) * q ^ n)) :=
      (ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg hC (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hq0 n)))
        hsum.summable).symm
    _ = ENNReal.ofReal (C * (q / (1 - q) ^ 2)) := by rw [hsum.tsum_eq]

theorem root_mass_finite_of_length_bounds (length : P → ℕ) (b : P → ℝ≥0∞)
    {C q : ℝ} (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcount : ∀ n, (∑' p : {p : P // length p = n}, b p) ≤
      ENNReal.ofReal (C * ((n : ℝ) * q ^ n))) :
    (∑' p, b p) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (root_mass_le_of_length_bounds length b hC hq0 hq1 hcount)

end RootedKP
