import RootedKP.BoundaryPrunedCounts

namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem side_prefix_10 : SidePrefixCheck 10 := by
  unfold SidePrefixCheck
  simp_rw [← prunedEndpointCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
