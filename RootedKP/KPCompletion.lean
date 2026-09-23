import RootedKP.LongPathCounting
import RootedKP.LoopKP

/-!
# Complete assembly from the remaining boundary-path counts

Only `UnweightedPathCountingInputs` remains to be constructed. In particular,
there is no loop-count or weighted-KP assumption in the final theorem below.
-/

namespace RootedKP.AKLT

theorem uniformKP_of_unweighted_path_counts (H : UnweightedPathCountingInputs) :
    UniformKPCondition :=
  uniformKP_of_counting_inputs (weighted_inputs_of_unweighted H) loop_kindMass_le_allowance

theorem scalar_bound_of_unweighted_path_counts (H : UnweightedPathCountingInputs)
    (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ENNReal) * ((7 / 10 : NNReal) : ENNReal) :=
  scalarSum_le_of_uniform_kp (uniformKP_of_unweighted_path_counts H) F cut

theorem uniform_rooted_summability_of_unweighted_path_counts
    (H : UnweightedPathCountingInputs) : UniformRootedSummability :=
  uniform_rooted_summability_of_uniform_kp (uniformKP_of_unweighted_path_counts H)

end RootedKP.AKLT
