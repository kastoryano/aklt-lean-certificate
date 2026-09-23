import RootedKP.BoundaryCounts
import RootedKP.FastLoopCounts

namespace RootedKP.BoundaryCounts

open Honeycomb BoundaryCharts Enumeration LoopCounts

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- List implementation of the exact chart search, avoiding repeated finite-set
construction. Its equality to the complete enumerator is proved below. -/
def fastCount (C : Chart) (accept : List Vertex → Prop) [DecidablePred accept] :
    ℕ → List Vertex → ℕ
  | 0, trail => if accept trail then 1 else 0
  | _ + 1, [] => 0
  | n + 1, u :: us =>
    (neighborList u).foldr (fun v acc =>
      (if (core C u ∨ core C v) ∧ v ∉ u :: us then
        fastCount C accept n (v :: u :: us) else 0) + acc) 0

theorem fastCount_eq (C : Chart) (accept : List Vertex → Prop) [DecidablePred accept]
    (n : ℕ) (trail : List Vertex) :
    fastCount C accept n trail = acceptedCount (next C) accept n trail := by
  induction n generalizing trail with
  | zero => rfl
  | succ n ih =>
    cases trail with
    | nil => rfl
    | cons u us =>
      simp only [fastCount, acceptedCount, next, Finset.filter_filter, Finset.sum_filter]
      cases u with
      | a q r =>
        have hq : q ≠ q - 1 := by omega
        have hr : r ≠ r - 1 := by omega
        simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
          hq, Ne.symm hq, hr, Ne.symm hr, ih, add_assoc, add_comm, add_left_comm]
      | b q r =>
        simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
          ih, add_assoc, add_comm, add_left_comm]

def fastCornerCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n,
    fastCount .corner (endsAt leftLeaf) n [.a ((k : ℤ) - 1) 1]

theorem fastCornerCount_eq (n : ℕ) : fastCornerCount n = cornerCount n := by
  simp only [fastCornerCount, cornerCount, fastCount_eq]

end RootedKP.BoundaryCounts
