import RootedKP.ShortRootCharts
import RootedKP.BoundaryPrunedCounts

namespace RootedKP.ShortRootCharts
open Honeycomb BoundaryCharts Enumeration LoopCounts BoundaryCounts

theorem accepted_endpoint_possible (root : Finset Vertex) (start : Vertex)
    (n : ℕ) (u : Vertex) (us result : List Vertex)
    (he : Extends (next .corner) n (u :: us) result)
    (ha : accepts root start result) : endpointPossible .corner n u := by
  apply endpointPossible_necessary .corner n u us result he
  cases result with
  | nil => exact False.elim ha.1
  | cons v vs => exact ha.1.1

def prunedRootCount (root : Finset Vertex) (n : ℕ) : ℕ :=
  ∑ start ∈ starts n, BoundaryCounts.prunedCount .corner (accepts root start)
    (endpointPossible .corner) n [start]

theorem prunedRootCount_eq (root : Finset Vertex) (n : ℕ) :
    prunedRootCount root n = count root n := by
  unfold prunedRootCount count
  apply Finset.sum_congr rfl
  intro start _
  exact BoundaryCounts.prunedCount_eq .corner _ _
    (accepted_endpoint_possible root start) n [start]

end RootedKP.ShortRootCharts
