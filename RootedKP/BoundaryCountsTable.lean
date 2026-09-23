import RootedKP.BoundaryCountCertificatesLong
import RootedKP.BoundaryCertificates.Q15
import RootedKP.BoundaryCertificates.Q17
import RootedKP.BoundaryCertificates.Q19
import RootedKP.BoundaryCertificates.R16
import RootedKP.BoundaryCertificates.R18
import RootedKP.BoundaryCertificates.R20
import Mathlib.Tactic.FinCases

/-! Complete exact local-chart R/Q tables, linked to the arithmetic input lists.
The corner count includes every crossing traversal by mem_cornerPaths_iff;
the side count bounds same-side corner traversals by BoundarySideBound.
Actual halo-to-chart transfer and endpoint orientation are separate bridges. -/
namespace RootedKP.BoundaryCounts

theorem full_corner_table :
    [cornerCount 3, cornerCount 5, cornerCount 7, cornerCount 9, cornerCount 11,
      cornerCount 13, cornerCount 15, cornerCount 17, cornerCount 19] = Arithmetic.oddCounts := by
  rw [cornerCount_three, cornerCount_five, cornerCount_seven, cornerCount_nine,
    cornerCount_eleven, cornerCount_thirteen, Q15, Q17, Q19]
  rfl

theorem full_side_table :
    [sideCount 8, sideCount 10, sideCount 12, sideCount 14,
      sideCount 16, sideCount 18, sideCount 20] = Arithmetic.evenCountsFrom8 := by
  rw [sideCount_eight, sideCount_ten, sideCount_twelve, sideCount_fourteen, R16, R18, R20]
  rfl

theorem cornerCount_at (k : Fin 9) :
    cornerCount (2 * k.val + 3) = Arithmetic.oddCounts[k.val]! := by
  fin_cases k <;> simp [Arithmetic.oddCounts, cornerCount_three, cornerCount_five,
    cornerCount_seven, cornerCount_nine, cornerCount_eleven, cornerCount_thirteen, Q15, Q17, Q19]

theorem sideCount_at (k : Fin 9) :
    sideCount (2 * k.val + 4) = ([1, 1] ++ Arithmetic.evenCountsFrom8)[k.val]! := by
  fin_cases k <;> simp [Arithmetic.evenCountsFrom8, sideCount_four, sideCount_six,
    sideCount_eight, sideCount_ten, sideCount_twelve, sideCount_fourteen, R16, R18, R20]

end RootedKP.BoundaryCounts
