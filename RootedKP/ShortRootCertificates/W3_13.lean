import RootedKP.ShortRootPruned
namespace RootedKP.ShortRootCharts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem w3_count_13 : count cornerRootThree 13 = 106 := by
  rw [← prunedRootCount_eq]
  decide +kernel
end RootedKP.ShortRootCharts
