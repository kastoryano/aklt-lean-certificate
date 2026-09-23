import RootedKP.PathCounting

/-!
# Analytic completion of the boundary-path tail estimate

The remaining input is an unweighted count for each length, stated on the
actual finite polymer set. All conversion to exponentially weighted sums and
the infinite tail are proved here.
-/

namespace RootedKP.AKLT

open scoped BigOperators Classical
open Arithmetic

noncomputable def tailTerm (b c : ℝ) (k : ℕ) : ℝ :=
  3 * (b / 16 + c * (2 * ((21 + k : ℕ) : ℝ) + 95) / 1024) *
    (qCap : ℝ) ^ (21 + k)

theorem tailTerm_hasSum (b c : ℝ) :
    HasSum (tailTerm b c) (b * (boundaryTail : ℝ) + c * (interiorTail : ℝ)) := by
  have hq0 : 0 ≤ (qCap : ℝ) := by norm_num [qCap, rCap]
  have hq1 : (qCap : ℝ) < 1 := by norm_num [qCap, rCap]
  have hg := geometric_tail (qCap : ℝ) hq0 hq1 21
  have hm := first_moment_tail (qCap : ℝ) hq0 hq1 21
  have hs := (hg.mul_left (3 * b / 16 + 285 * c / 1024)).add
    (hm.mul_left (6 * c / 1024))
  convert hs using 1
  · funext k
    unfold tailTerm
    ring
  · unfold boundaryTail interiorTail tail0 tail1
    push_cast
    ring

theorem tailTerm_nonneg {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (k : ℕ) :
    0 ≤ tailTerm b c k := by
  unfold tailTerm qCap rCap
  positivity

/-- A combinatorial lengthwise estimate suffices for the exact tail constants.
`b` counts boundary-endpoint contributions and `c` the internal root vertices. -/
theorem tail_envelope_le_of_counts {F : Honeycomb.Rectangle} (p : Polymer F)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcount : ∀ n, 21 ≤ n →
      (((tailPathSet p).filter fun q => q.length = n).card : ℝ) ≤
        (b / 16 + c * (2 * (n : ℝ) + 95) / 1024) * (2 : ℝ) ^ n) :
    tailPathEnvelope p ≤ b * (boundaryTail : ℝ) + c * (interiorTail : ℝ) := by
  classical
  let N := (tailPathSet p).sup Polymer.length + 1
  have hlen : ∀ q ∈ tailPathSet p, 21 ≤ q.length ∧ q.length < 21 + N := by
    intro q hq
    have hn := (Finset.mem_filter.mp hq).2
    have hu := Finset.le_sup (f := Polymer.length) hq
    exact ⟨by omega, by dsimp [N]; omega⟩
  calc
    tailPathEnvelope p = ∑ i ∈ Finset.range N,
        (((tailPathSet p).filter fun q => q.length = 21 + i).card : ℝ) *
          (weightCap (21 + i) : ℝ) :=
      weighted_sum_by_length (tailPathSet p) Polymer.length
        (fun n => (weightCap n : ℝ)) 21 N hlen
    _ ≤ ∑ i ∈ Finset.range N, tailTerm b c i := by
      apply Finset.sum_le_sum
      intro i _
      have hw : 0 ≤ (weightCap (21 + i) : ℝ) := by
        exact_mod_cast weightCap_nonneg (21 + i)
      have h := mul_le_mul_of_nonneg_right (hcount (21 + i) (by omega)) hw
      apply h.trans_eq
      rw [weightCap_eq_long (21 + i) (by omega)]
      push_cast
      have hp : (2 : ℝ) ^ (21 + i) * (rCap : ℝ) ^ (21 + i) =
          (qCap : ℝ) ^ (21 + i) := by
        rw [← mul_pow]
        congr 1
        norm_num [qCap]
      unfold tailTerm
      calc
        _ = 3 * (b / 16 + c * (2 * ((21 + i : ℕ) : ℝ) + 95) / 1024) *
            ((2 : ℝ) ^ (21 + i) * (rCap : ℝ) ^ (21 + i)) := by push_cast; ring
        _ = _ := by rw [hp]
    _ ≤ _ := sum_le_hasSum _ (fun i _ => tailTerm_nonneg hb hc i) (tailTerm_hasSum b c)

noncomputable def boundaryCharge {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ :=
  if p.kind = .path then 1 else 0

noncomputable def internalCharge {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ :=
  if p.kind = .path then (p.length : ℝ) - 2 else (p.length : ℝ)

/-- Pure combinatorial tail input on canonical regional polymers. -/
def TailLengthCountBound : Prop := ∀ (F : Honeycomb.Rectangle) (p : Polymer F)
    (n : ℕ), 21 ≤ n →
    (((tailPathSet p).filter fun q => q.length = n).card : ℝ) ≤
      (boundaryCharge p / 16 + internalCharge p * (2 * (n : ℝ) + 95) / 1024) *
        (2 : ℝ) ^ n

theorem boundaryTail_le_two_interiorTail : boundaryTail ≤ 2 * interiorTail := by
  norm_num [boundaryTail, interiorTail, tail0, tail1, qCap, rCap]

theorem tail_allowance_of_length_counts (H : TailLengthCountBound)
    (F : Honeycomb.Rectangle) (p : Polymer F) :
    tailPathEnvelope p ≤ (tailEnvelopeAllowance p : ℝ) := by
  have hb : 0 ≤ boundaryCharge p := by unfold boundaryCharge; split_ifs <;> norm_num
  have hc : 0 ≤ internalCharge p := by
    unfold internalCharge
    split_ifs
    · have h := p.length_ge_three
      have h' : (3 : ℝ) ≤ p.length := by exact_mod_cast h
      linarith
    · positivity
  have h := tail_envelope_le_of_counts p hb hc (H F p)
  cases hk : p.kind with
  | path =>
      simp only [boundaryCharge, internalCharge, hk, ite_true, one_mul] at h
      by_cases hn : p.length ≤ 6
      · simpa [tailEnvelopeAllowance, hn, hk] using h
      · have hb' : (boundaryTail : ℝ) ≤ 2 * (interiorTail : ℝ) := by
          exact_mod_cast boundaryTail_le_two_interiorTail
        simp only [tailEnvelopeAllowance, if_neg hn, Rat.cast_mul, Rat.cast_natCast]
        nlinarith
  | loop =>
      simp [boundaryCharge, internalCharge, hk] at h
      by_cases hn : p.length ≤ 6
      · have hl : p.length = 6 := le_antisymm hn (p.loop_length_ge_six hk)
        simpa [tailEnvelopeAllowance, hn, hk, hl] using h
      · simpa [tailEnvelopeAllowance, hn] using h

/-- Build the weighted path-counting interface using only unweighted tail
counts, short cumulative counts, and the finite long-root geometric estimate. -/
theorem pathCountingInputs_of_counts
    (hshort : ∀ (F : Honeycomb.Rectangle) (p : Polymer F), p.length ≤ 6 →
      CumulativePathBound p (if p.kind = .path then shortCounts p.length else L6Counts))
    (hlong : ∀ (F : Honeycomb.Rectangle) (p : Polymer F), 7 ≤ p.length →
      shortPathEnvelope p ≤ (longFiniteUniformAllowance p.length : ℝ))
    (htail : TailLengthCountBound) : PathCountingInputs :=
  ⟨hshort, hlong, tail_allowance_of_length_counts htail⟩

end RootedKP.AKLT
