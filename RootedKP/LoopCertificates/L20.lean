import RootedKP.FastLoopCounts

namespace RootedKP.LoopCounts
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem loops20 : (anchoredLoops 20).card = 920 := by
  unfold anchoredLoops
  rw [← acceptedCount_eq_card, ← prunedCount_eq, ← fastCount_eq]
  decide +kernel

end RootedKP.LoopCounts
#print axioms RootedKP.LoopCounts.loops20
