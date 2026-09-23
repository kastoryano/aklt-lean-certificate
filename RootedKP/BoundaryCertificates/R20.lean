import RootedKP.BoundarySharpCounts
namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem R20 : sideCount 20 = 1943 := by
  rw [← sharpSideCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
