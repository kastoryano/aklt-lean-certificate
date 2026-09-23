import RootedKP.PackedSupports
import RootedKP.CatalogStartPruning

/-! Enumerate each boundary path once, independently of the root. The result
retains multiplicities and stores each support as a proved exact bit mask. -/
namespace RootedKP.CachedPaths
open Honeycomb BoundaryCharts BoundaryCounts ShortRootCharts PackedSupports
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def endpointAccept (start : Vertex) : List Vertex → Prop :=
  endsAt (fun finish => leafCode .corner finish ∧ leafBefore start finish)

instance (start : Vertex) : DecidablePred (endpointAccept start) := by
  unfold endpointAccept
  infer_instance

def gather (start : Vertex) : ℕ → List Vertex → List ℕ
  | 0,trail => if endpointAccept start trail then [pack trail] else []
  | _+1,[] => []
  | n+1,u::us =>
    if endpointPossible .corner (n+1) u then
      (LoopCounts.neighborList u).foldr (fun v acc =>
        (if (core .corner u ∨ core .corner v) ∧ v∉u::us then
          gather start n (v::u::us) else [])++acc) []
    else []

def hitCount (rootMask : ℕ) (masks : List ℕ) : ℕ :=
  masks.countP (fun m => rootMask &&& m != 0)

theorem hitCount_append (r : ℕ) (xs ys : List ℕ) :
    hitCount r (xs++ys)=hitCount r xs+hitCount r ys := by simp [hitCount]

theorem hitCount_gather (root : List Vertex) (start : Vertex) (n : ℕ) (trail : List Vertex) :
    hitCount (pack root) (gather start n trail)=
      prunedCount .corner (accepts root.toFinset start) (endpointPossible .corner) n trail := by
  induction n generalizing trail with
  | zero =>
    by_cases ha : endpointAccept start trail
    · dsimp only [endpointAccept] at ha
      simp [gather,prunedCount,endpointAccept,ha,hitCount,accepts,overlap_hitsRoot]
    · dsimp only [endpointAccept] at ha
      simp [gather,prunedCount,endpointAccept,ha,hitCount,accepts]
  | succ n ih =>
    cases trail with
    | nil => rfl
    | cons u us =>
      by_cases hp : endpointPossible .corner (n+1) u
      · simp only [gather,prunedCount,if_pos hp]
        generalize LoopCounts.neighborList u=ns
        induction ns with
        | nil => rfl
        | cons v ns ihn =>
          simp only [List.foldr_cons,hitCount_append,ihn]
          by_cases hv : (core .corner u ∨ core .corner v) ∧ v∉u::us
          · simp only [if_pos hv,ih]
          · simp only [if_neg hv,hitCount,List.countP_nil,Nat.zero_add]
      · simp [gather,prunedCount,if_neg hp,hitCount]

def upperStart (k : ℕ) : Vertex := .a ((k : ℤ)-1) 1
def leftStart (k : ℕ) : Vertex := .b (-2) (-(k : ℤ))

def cachedCatalogCount (root : List Vertex) (n : ℕ) : ℕ :=
  ∑start∈starts 62,hitCount (pack root) (gather start n [start])

theorem cachedCatalogCount_eq (root : List Vertex) (n : ℕ) :
    cachedCatalogCount root n=ShortRootRepresentatives.catalogCount root.toFinset n := by
  simp only [cachedCatalogCount,ShortRootRepresentatives.catalogCount,hitCount_gather]

end RootedKP.CachedPaths
