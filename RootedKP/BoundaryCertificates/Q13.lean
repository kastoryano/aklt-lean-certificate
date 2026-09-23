import RootedKP.BoundaryPrunedCounts
namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem Q13 : cornerCount 13 = 202 := by
  rw [← prunedCornerCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
