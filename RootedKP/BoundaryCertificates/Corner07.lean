import RootedKP.BoundaryPrunedCounts

namespace RootedKP.BoundaryCounts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem corner_prefix_7 : CornerPrefixCheck 7 := by
  unfold CornerPrefixCheck
  simp_rw [← prunedEndpointCount_eq]
  decide +kernel

end RootedKP.BoundaryCounts
