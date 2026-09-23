import RootedKP.ShortRootPruned
namespace RootedKP.ShortRootCharts
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem w3_count_09 : count cornerRootThree 9 = 14 := by
  rw [← prunedRootCount_eq]
  decide +kernel
end RootedKP.ShortRootCharts
