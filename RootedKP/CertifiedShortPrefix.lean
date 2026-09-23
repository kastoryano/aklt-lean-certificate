import RootedKP.CertifiedPathPrefixes
import RootedKP.PathCache.RowsLoop
import RootedKP.PathCache.RootsLoop

namespace RootedKP.CachedPaths
open Honeycomb PackedSupports ShortRootRepresentatives Arithmetic
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem mappedRowsLoop : rowsLoop.map Prod.fst=rootMasksLoop := by decide +kernel

theorem prefixLoop (entry : Vertex × List Vertex) (hr : entry∈loopRootTrails)
    (k : Fin 13) :
    (∑i∈Finset.range k.val,catalogCount entry.2.toFinset (3+i))≤
      ∑i∈Finset.range k.val,L6Counts[i]?.getD 0 := by
  apply catalog_prefix_of_rows rowsLoop L6Counts verifiedRowsLoop entry.2
  rw [mappedRowsLoop]
  exact coversLoop entry hr

end RootedKP.CachedPaths

namespace RootedKP.AKLT
open CachedPaths

/-- All finite numerical inputs are proved; no catalog bound is assumed. -/
theorem shortPrefixCatalogBounds : ShortPrefixCatalogBounds := by
  constructor
  · intro ell
    fin_cases ell
    · exact prefixFour
    · exact prefixFive
    · exact prefixSix
  · exact prefixLoop

end RootedKP.AKLT
