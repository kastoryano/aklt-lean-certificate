import RootedKP.ShortPrefixCompletion
import RootedKP.CatalogStartPruning
namespace RootedKP.ShortRootRepresentatives
open Honeycomb
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem bench_count : fastCatalogCount ({Vertex.a (-1) (-1),Vertex.a (-1) (0),Vertex.a (-1) (1),Vertex.b (-2) (-1),Vertex.b (-1) (-1),Vertex.b (-1) (0)} : Finset Vertex) 14 = 225 := by
  decide +kernel
end RootedKP.ShortRootRepresentatives
