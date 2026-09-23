import RootedKP.ShortPrefixCompletion
import RootedKP.CodeCountCertificates
namespace RootedKP.CachedPaths
open Honeycomb PackedSupports ShortRootRepresentatives Arithmetic
open scoped BigOperators
set_option maxHeartbeats 0
theorem catalog_prefix_of_rows (rows : List (ℕ × List ℕ)) (bounds : List ℕ)
    (hc : ∀row∈rows,rowChecked allMasks bounds row)
    (root : List Vertex) (hr : pack root∈rows.map Prod.fst) (k : Fin 13) :
    (∑i∈Finset.range k.val,catalogCount root.toFinset (3+i))≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0 := by
  calc
    _ = ∑i∈Finset.range k.val,hitCount (pack root) (allMasks (3+i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact catalogCount_eq_allMasks root ⟨i,by have := Finset.mem_range.mp hi; omega⟩
    _ ≤ _ := prefix_of_checked_rows allMasks bounds rows hc (pack root) hr k

end RootedKP.CachedPaths
