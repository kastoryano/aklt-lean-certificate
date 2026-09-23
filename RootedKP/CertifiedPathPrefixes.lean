import RootedKP.CatalogPrefixRows
import RootedKP.PathCache.RowsFour
import RootedKP.PathCache.RootsFour
import RootedKP.PathCache.RowsFive
import RootedKP.PathCache.RootsFive
import RootedKP.PathCache.RowsSix
import RootedKP.PathCache.RootsSix

namespace RootedKP.CachedPaths
open Honeycomb PackedSupports ShortRootRepresentatives Arithmetic
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem mappedRowsFour : rowsFour.map Prod.fst=rootMasksFour := by decide +kernel

theorem prefixFour (root : List Vertex) (hr : root∈boundaryRootTrails 4)
    (k : Fin 13) :
    (∑i∈Finset.range k.val,catalogCount root.toFinset (3+i))≤
      ∑i∈Finset.range k.val,W4Counts[i]?.getD 0 := by
  apply catalog_prefix_of_rows rowsFour W4Counts verifiedRowsFour root
  rw [mappedRowsFour]
  exact coversFour root hr

theorem mappedRowsFive : rowsFive.map Prod.fst=rootMasksFive := by decide +kernel

theorem prefixFive (root : List Vertex) (hr : root∈boundaryRootTrails 5)
    (k : Fin 13) :
    (∑i∈Finset.range k.val,catalogCount root.toFinset (3+i))≤
      ∑i∈Finset.range k.val,W5Counts[i]?.getD 0 := by
  apply catalog_prefix_of_rows rowsFive W5Counts verifiedRowsFive root
  rw [mappedRowsFive]
  exact coversFive root hr

theorem mappedRowsSix : rowsSix.map Prod.fst=rootMasksSix := by decide +kernel

theorem prefixSix (root : List Vertex) (hr : root∈boundaryRootTrails 6)
    (k : Fin 13) :
    (∑i∈Finset.range k.val,catalogCount root.toFinset (3+i))≤
      ∑i∈Finset.range k.val,W6Counts[i]?.getD 0 := by
  apply catalog_prefix_of_rows rowsSix W6Counts verifiedRowsSix root
  rw [mappedRowsSix]
  exact coversSix root hr

end RootedKP.CachedPaths
