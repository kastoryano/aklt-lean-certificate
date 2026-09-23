import RootedKP.KPAccounting
import RootedKP.FiniteCounting
import RootedKP.ProbeRootCounting

/-!
# From actual boundary-path counts to the scalar KP accounting

Short-root data are cumulative count bounds, not lengthwise maxima.
The remaining geometric/enumerative hypotheses are grouped at the end.
-/

namespace RootedKP.AKLT

open scoped BigOperators Classical
open Arithmetic

noncomputable def shortPathSet {F : Honeycomb.Rectangle} (p : Polymer F) : Finset (Polymer F) :=
  (kindSet p .path).filter (fun q => q.length ≤ 20)

noncomputable def tailPathSet {F : Honeycomb.Rectangle} (p : Polymer F) : Finset (Polymer F) :=
  (kindSet p .path).filter (fun q => ¬ q.length ≤ 20)

noncomputable def shortPathEnvelope {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ :=
  ∑ q ∈ shortPathSet p, (weightCap q.length : ℝ)

noncomputable def tailPathEnvelope {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ :=
  ∑ q ∈ tailPathSet p, (weightCap q.length : ℝ)

noncomputable def pathLengthCount {F : Honeycomb.Rectangle} (p : Polymer F) (i : ℕ) : ℕ :=
  ((shortPathSet p).filter (fun q => q.length = 3 + i)).card

def CumulativePathBound {F : Honeycomb.Rectangle} (p : Polymer F) (cs : List ℕ) : Prop :=
  cs.length = 18 ∧ ∀ k ≤ 18,
    prefixSum (fun i => (pathLengthCount p i : ℝ)) k ≤
      prefixSum (fun i => (cs[i]?.getD 0 : ℝ)) k

theorem short_envelope_le_of_cumulative {F : Honeycomb.Rectangle} (p : Polymer F)
    (cs : List ℕ) (hc : CumulativePathBound p cs) :
    shortPathEnvelope p ≤ (sumCounts weightCap 3 1 cs : ℝ) := by
  classical
  obtain ⟨hlen, hcum⟩ := hc
  calc
    shortPathEnvelope p ≤ ∑ i ∈ Finset.range 18,
        (cs[i]?.getD 0 : ℝ) * (weightCap (3 + i) : ℝ) := by
      apply weighted_sum_le_of_cumulative_counts
        (shortPathSet p) Polymer.length 3 18 (fun n => (weightCap n : ℝ))
        (fun i => (cs[i]?.getD 0 : ℝ))
      · intro q hq
        have hh := (Finset.mem_filter.mp hq).2
        exact ⟨q.length_ge_three, by omega⟩
      · intro i _
        exact_mod_cast weightCap_nonneg (3 + i)
      · intro i _
        have hd := weightCap_decreasing (3 + i) (by omega)
        exact_mod_cast hd
      · exact hcum
    _ = _ := by
      symm
      simpa only [hlen, Nat.one_mul] using sumCounts_eq_sum_range weightCap 3 1 cs

theorem kind_path_mass_le_envelopes {F : Honeycomb.Rectangle} (p : Polymer F) :
    kindMass p .path ≤ (5 / 6 : ℝ) * (shortPathEnvelope p + tailPathEnvelope p) := by
  classical
  calc
    kindMass p .path ≤ ∑ q ∈ kindSet p .path, (5 / 6 : ℝ) * (weightCap q.length : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact path_budget_le_weightCap q (Finset.mem_filter.mp hq).2.1
    _ = (5 / 6 : ℝ) * ∑ q ∈ kindSet p .path, (weightCap q.length : ℝ) :=
      (Finset.mul_sum ..).symm
    _ = _ := by
      congr 1
      exact (Finset.sum_filter_add_sum_filter_not (kindSet p .path)
        (fun q => q.length ≤ 20) (fun q => (weightCap q.length : ℝ))).symm

def shortEnvelopeAllowance {F : Honeycomb.Rectangle} (p : Polymer F) : ℚ :=
  if p.length ≤ 6 then
    sumCounts weightCap 3 1 (if p.kind = .path then shortCounts p.length else L6Counts)
  else longFiniteUniformAllowance p.length

def tailEnvelopeAllowance {F : Honeycomb.Rectangle} (p : Polymer F) : ℚ :=
  if p.length ≤ 6 then
    if p.kind = .path then boundaryTail + ((p.length : ℚ) - 2) * interiorTail
    else 6 * interiorTail
  else (p.length : ℚ) * interiorTail

theorem pathAllowance_eq_envelopes {F : Honeycomb.Rectangle} (p : Polymer F) :
    pathAllowance p = pathFactor * (shortEnvelopeAllowance p + tailEnvelopeAllowance p) := by
  unfold pathAllowance shortEnvelopeAllowance tailEnvelopeAllowance
  split_ifs <;> ring

/-- Exact remaining path-counting obligations. The short-root part asks only
for cumulative unweighted counts; decreasing weights and all scalar algebra
are supplied by the proved lemmas above. -/
structure PathCountingInputs : Prop where
  shortRoots : ∀ (F : Honeycomb.Rectangle) (p : Polymer F), p.length ≤ 6 →
    CumulativePathBound p (if p.kind = .path then shortCounts p.length else L6Counts)
  longRoots : ∀ (F : Honeycomb.Rectangle) (p : Polymer F), 7 ≤ p.length →
    shortPathEnvelope p ≤ (longFiniteUniformAllowance p.length : ℝ)
  tails : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
    tailPathEnvelope p ≤ (tailEnvelopeAllowance p : ℝ)

theorem path_mass_bound_of_counts (H : PathCountingInputs)
    (F : Honeycomb.Rectangle) (p : Polymer F) :
    kindMass p .path ≤ (pathAllowance p : ℝ) := by
  have hs : shortPathEnvelope p ≤ (shortEnvelopeAllowance p : ℝ) := by
    by_cases hn : p.length ≤ 6
    · simpa only [shortEnvelopeAllowance, if_pos hn] using
        short_envelope_le_of_cumulative p _ (H.shortRoots F p hn)
    · simpa only [shortEnvelopeAllowance, if_neg hn] using H.longRoots F p (by omega)
  apply (kind_path_mass_le_envelopes p).trans
  rw [pathAllowance_eq_envelopes]
  norm_num only [pathFactor, Rat.cast_mul, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left (add_le_add hs (H.tails F p)) (by norm_num)

theorem uniformKP_of_counting_inputs (H : PathCountingInputs)
    (hloop : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
      kindMass p .loop ≤ (loopAllowance p : ℝ)) : UniformKPCondition :=
  uniformKP_of_kind_mass_bounds (path_mass_bound_of_counts H) hloop

theorem scalar_bound_of_counting_inputs (H : PathCountingInputs)
    (hloop : ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
      kindMass p .loop ≤ (loopAllowance p : ℝ))
    (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ENNReal) * ((7 / 10 : NNReal) : ENNReal) :=
  scalarSum_le_of_uniform_kp (uniformKP_of_counting_inputs H hloop) F cut

end RootedKP.AKLT
