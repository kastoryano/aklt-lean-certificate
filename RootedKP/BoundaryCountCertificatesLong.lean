import RootedKP.BoundaryCountCertificates
import RootedKP.BoundaryCertificates.Q13
import RootedKP.BoundaryCertificates.R14

namespace RootedKP.BoundaryCounts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem cornerCount_thirteen : cornerCount 13 = 202 := Q13

theorem sideCount_fourteen : sideCount 14 = 75 := R14

theorem corner_prefix_six_matches_arithmetic :
    [cornerCount 3, cornerCount 5, cornerCount 7, cornerCount 9,
      cornerCount 11, cornerCount 13] = Arithmetic.oddCounts.take 6 := by
  rw [cornerCount_three, cornerCount_five, cornerCount_seven,
    cornerCount_nine, cornerCount_eleven, cornerCount_thirteen]
  rfl

theorem side_prefix_four_matches_arithmetic :
    [sideCount 8, sideCount 10, sideCount 12, sideCount 14] =
      Arithmetic.evenCountsFrom8.take 4 := by
  rw [sideCount_eight, sideCount_ten, sideCount_twelve, sideCount_fourteen]
  rfl

end RootedKP.BoundaryCounts
