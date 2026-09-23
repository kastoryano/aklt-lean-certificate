import RootedKP.BoundaryPrunedCounts
namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem R14 : sideCount 14 = 75 := by
  rw [← prunedSideCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
