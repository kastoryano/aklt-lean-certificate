import RootedKP.BoundaryPrunedCounts
namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem R18 : sideCount 18 = 649 := by
  rw [← prunedSideCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
