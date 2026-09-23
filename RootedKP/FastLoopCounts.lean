import RootedKP.LoopCounts

namespace RootedKP.LoopCounts

open Honeycomb

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def neighborList : Vertex → List Vertex
  | .a q r => [.b q r, .b (q - 1) r, .b q (r - 1)]
  | .b q r => [.a q r, .a (q + 1) r, .a q (r + 1)]

/-- List-based implementation with the same verified distance pruning. -/
def fastCount : ℕ → List Vertex → ℕ
  | 0, trail => if closes trail then 1 else 0
  | _ + 1, [] => 0
  | n + 1, u :: us =>
      if withinClosingDistance (n + 1) u then
        (neighborList u).foldr (fun v acc =>
          (if v ∈ u :: us then 0 else fastCount n (v :: u :: us)) + acc) 0
      else 0

theorem fastCount_eq (n : ℕ) (trail : List Vertex) :
    fastCount n trail = prunedCount n trail := by
  induction n generalizing trail with
  | zero => rfl
  | succ n ih =>
      cases trail with
      | nil => rfl
      | cons u us =>
          by_cases h : withinClosingDistance (n + 1) u
          · simp only [fastCount, prunedCount, if_pos h, Finset.sum_filter]
            cases u with
            | a q r =>
                have hq : q ≠ q - 1 := by omega
                have hr : r ≠ r - 1 := by omega
                simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
                  hq, Ne.symm hq, hr, Ne.symm hr, ih, add_assoc, add_comm, add_left_comm]
            | b q r =>
                simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
                  ih, add_assoc, add_comm, add_left_comm]
          · simp only [fastCount, prunedCount, if_neg h]

end RootedKP.LoopCounts

#print axioms RootedKP.LoopCounts.fastCount_eq
