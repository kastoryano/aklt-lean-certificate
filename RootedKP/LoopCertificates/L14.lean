import RootedKP.FastLoopCounts

namespace RootedKP.LoopCounts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem loops14 : (anchoredLoops 14).card = 56 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card, ← prunedCount_eq, ← fastCount_eq]
  decide +kernel

end RootedKP.LoopCounts
#print axioms RootedKP.LoopCounts.loops14
