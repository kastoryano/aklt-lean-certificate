import RootedKP.BoundaryPrefixes
import RootedKP.BoundaryChartLeaves

namespace RootedKP.BoundaryCounts
open Honeycomb BoundaryCharts Enumeration LoopCounts

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def endpointFastCount (C : Chart) : ℕ → Vertex → Vertex → ℕ
  | 0, u, _ => if leafCode C u then 1 else 0
  | n + 1, u, forbidden =>
    (neighborList u).foldr (fun v acc =>
      (if (core C u ∨ core C v) ∧ v ≠ forbidden then
        fastCount C (endsAt (leafCode C)) n [v, u] else 0) + acc) 0

theorem endpointFastCount_eq (C : Chart) (n : ℕ) (u forbidden : Vertex) :
    endpointFastCount C n u forbidden = endpointCount C n u forbidden := by
  have hleaf : leafCode C = Leaf C := funext fun v => propext (leafCode_iff C v)
  cases n with
  | zero => simp only [endpointFastCount, endpointCount, hleaf]
  | succ n =>
    simp only [endpointFastCount, endpointCount, fastCount_eq, hleaf]
    have herase : (next C u).erase forbidden = (next C u).filter (fun v => v ≠ forbidden) := by
      ext v
      simp only [Finset.mem_erase, Finset.mem_filter, and_comm]
    rw [herase]
    simp only [next, Finset.filter_filter, Finset.sum_filter]
    cases u with
    | a q r =>
        have hq : q ≠ q - 1 := by omega
        have hr : r ≠ r - 1 := by omega
        simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
          hq, Ne.symm hq, hr, add_comm, add_left_comm, add_assoc]
    | b q r =>
        simp [neighborList, neighbors, Finset.sum_insert, Finset.sum_singleton,
          add_comm, add_left_comm, add_assoc]

/-- Indexing both vertex phases and all three ambient edge directions. -/
def phaseVertex (t : Fin 2) (q r : ℤ) : Vertex :=
  if t.val = 0 then .a q r else .b q r

def neighborAt : Vertex → Fin 3 → Vertex
  | .a q r, i => match i.val with
      | 0 => .b q r | 1 => .b (q - 1) r | _ => .b q (r - 1)
  | .b q r, i => match i.val with
      | 0 => .a q r | 1 => .a (q + 1) r | _ => .a q (r + 1)

/-- Safe envelope from the appendix. Each entry is tested against actual chart
searches below, not merely against a second copy of the input numerals. -/
def prefixCap : ℕ → ℕ
  | 1 => 1 | 2 => 2 | 3 => 2 | 4 => 4 | 5 => 6
  | 6 => 8 | 7 => 16 | 8 => 24 | 9 => 40 | 10 => 64 | _ => 0

def SidePrefixCheck (n : ℕ) : Prop :=
  ∀ (t : Fin 2) (q : Fin 6) (i : Fin 3),
    let u := phaseVertex t ((q.val : ℤ) - 4) 0
    let f := neighborAt u i
    (core .side u ∨ core .side f) → endpointFastCount .side n u f ≤ prefixCap n

def CornerPrefixCheck (n : ℕ) : Prop :=
  ∀ (t : Fin 2) (q r : Fin 6) (i : Fin 3),
    let u := phaseVertex t ((q.val : ℤ) - 2) ((r.val : ℤ) - 4)
    let f := neighborAt u i
    (core .corner u ∨ core .corner f) → endpointFastCount .corner n u f ≤ prefixCap n

instance (n : ℕ) : Decidable (SidePrefixCheck n) := by
  unfold SidePrefixCheck
  infer_instance
instance (n : ℕ) : Decidable (CornerPrefixCheck n) := by
  unfold CornerPrefixCheck
  infer_instance

end RootedKP.BoundaryCounts
