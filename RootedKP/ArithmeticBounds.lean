import RootedKP.Arithmetic

/-!
# Undivided scalar allowances for actual root lengths

These identities turn the finite ratio checks into bounds on the numerator
at every long-root length. They make no claim about graph-count coverage.
-/

namespace RootedKP.Arithmetic

set_option maxHeartbeats 0

def shortPathAllowance (ell : ℕ) (counts : List ℕ) : ℚ :=
  pathFactor * (sumCounts weightCap 3 1 counts + boundaryTail +
    ((ell : ℚ) - 2) * interiorTail) + ((ell : ℚ) - 2) * loopMass

def shortLoopAllowance : ℚ :=
  pathFactor * (sumCounts weightCap 3 1 L6Counts + 6 * interiorTail) + 6 * loopMass

def longFinitePathAllowance (ell : ℚ) : ℚ :=
  (ell / 2 + 1) * weightCap 4 + 2 * ell * weightCap 6 +
    sumCounts (fun n => (ell / 2 + collarCoefficient n) * weightCap n)
      8 2 evenCountsFrom8 + sumCounts weightCap 3 2 oddCounts

def longAllowance (ell : ℚ) : ℚ :=
  pathFactor * (longFinitePathAllowance ell + ell * interiorTail) + ell * loopMass

/-- Uniform long-root allowance: the single-corner expression at the minimum
length seven is scaled by root length. This pays for roots meeting multiple
separated corner patches; the unscaled additive odd-path term is insufficient. -/
def longFiniteUniformAllowance (ell : ℚ) : ℚ :=
  ell * (longFinitePathAllowance 7 / 7)

def longUniformAllowance (ell : ℚ) : ℚ :=
  pathFactor * (longFiniteUniformAllowance ell + ell * interiorTail) + ell * loopMass

def longSlope : ℚ :=
  pathFactor * (weightCap 4 / 2 + 2 * weightCap 6 +
    sumCounts (fun n => weightCap n / 2) 8 2 evenCountsFrom8 + interiorTail) + loopMass

def longIntercept : ℚ :=
  pathFactor * (weightCap 4 +
    sumCounts (fun n => collarCoefficient n * weightCap n) 8 2 evenCountsFrom8 +
    sumCounts weightCap 3 2 oddCounts)

theorem longAllowance_affine (ell : ℚ) :
    longAllowance ell = ell * longSlope + longIntercept := by
  unfold longAllowance longFinitePathAllowance longSlope longIntercept
  simp only [evenCountsFrom8, oddCounts, sumCounts]
  ring

theorem longIntercept_nonneg : 0 ≤ longIntercept := by
  norm_num [longIntercept, pathFactor, weightCap, rCap, collarCoefficient,
    sumCounts, evenCountsFrom8, oddCounts]

theorem longAllowance_seven : longAllowance 7 < slope * 7 := by
  have h := long_path_ratio
  have heq : longAllowance 7 = longRatio 7 * slope * 7 := by
    unfold longAllowance longFinitePathAllowance longRatio
    simp only [evenCountsFrom8, oddCounts, sumCounts]
    norm_num [slope]
    ring
  rw [heq]
  norm_num [slope] at *
  linarith

theorem longUniformAllowance_le_cost (ell : ℚ) (hell : 0 ≤ ell) :
    longUniformAllowance ell ≤ slope * ell := by
  have h := mul_le_mul_of_nonneg_left (longAllowance_seven.le)
    (show 0 ≤ ell / 7 by positivity)
  have heq : longUniformAllowance ell = (ell / 7) * longAllowance 7 := by
    unfold longUniformAllowance longFiniteUniformAllowance longAllowance
    ring
  rw [heq]
  convert h using 1 <;> ring

/-- The checked long-root ratio at seven suffices uniformly for all larger
lengths. No finite extrapolation is assumed. -/
theorem longAllowance_le_cost (ell : ℚ) (hell : 7 ≤ ell) :
    longAllowance ell ≤ slope * ell := by
  have h7 := longAllowance_seven
  have hb := longIntercept_nonneg
  rw [longAllowance_affine] at h7 ⊢
  have hs : longSlope ≤ slope := by linarith
  have hm := mul_nonneg (sub_nonneg.mpr hell) (sub_nonneg.mpr hs)
  nlinarith

theorem W3_allowance : shortPathAllowance 3 W3Counts ≤ a 3 := by
  have h := W3_ratio
  change shortPathAllowance 3 W3Counts / a 3 < _ at h
  norm_num [a] at h ⊢
  linarith

theorem W4_allowance : shortPathAllowance 4 W4Counts ≤ a 4 := by
  have h := W4_ratio
  change shortPathAllowance 4 W4Counts / a 4 < _ at h
  norm_num [a] at h ⊢
  linarith

theorem W5_allowance : shortPathAllowance 5 W5Counts ≤ a 5 := by
  have h := W5_ratio
  change shortPathAllowance 5 W5Counts / a 5 < _ at h
  norm_num [a] at h ⊢
  linarith

theorem W6_allowance : shortPathAllowance 6 W6Counts ≤ a 6 := by
  have h := W6_ratio
  change shortPathAllowance 6 W6Counts / a 6 < _ at h
  norm_num [a] at h ⊢
  linarith

theorem L6_allowance : shortLoopAllowance ≤ a 6 := by
  have h := L6_ratio
  change shortLoopAllowance / a 6 < _ at h
  norm_num [a] at h ⊢
  linarith

end RootedKP.Arithmetic
