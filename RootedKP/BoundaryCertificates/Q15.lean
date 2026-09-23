import RootedKP.BoundaryPrunedCounts
namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem Q15 : cornerCount 15 = 647 := by
  rw [← prunedCornerCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
