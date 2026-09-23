import RootedKP.BoundaryPrunedCounts

namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem side_prefix_6 : SidePrefixCheck 6 := by
  unfold SidePrefixCheck
  simp_rw [← prunedEndpointCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
