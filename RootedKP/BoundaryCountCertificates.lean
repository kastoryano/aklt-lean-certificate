import RootedKP.BoundaryFastCounts

namespace RootedKP.BoundaryCounts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem cornerCount_nine : cornerCount 9 = 20 := by
  rw [← fastCornerCount_eq]
  decide +kernel
theorem cornerCount_eleven : cornerCount 11 = 64 := by
  rw [← fastCornerCount_eq]
  decide +kernel
theorem sideCount_ten : sideCount 10 = 9 := by
  unfold sideCount
  rw [← fastCount_eq]
  decide +kernel
theorem sideCount_twelve : sideCount 12 = 26 := by
  unfold sideCount
  rw [← fastCount_eq]
  decide +kernel

theorem corner_prefix_five_matches_arithmetic :
    [cornerCount 3, cornerCount 5, cornerCount 7, cornerCount 9, cornerCount 11] =
      Arithmetic.oddCounts.take 5 := by
  rw [cornerCount_three, cornerCount_five, cornerCount_seven,
    cornerCount_nine, cornerCount_eleven]
  rfl

theorem side_prefix_three_matches_arithmetic :
    [sideCount 8, sideCount 10, sideCount 12] = Arithmetic.evenCountsFrom8.take 3 := by
  rw [sideCount_eight, sideCount_ten, sideCount_twelve]
  rfl

end RootedKP.BoundaryCounts
