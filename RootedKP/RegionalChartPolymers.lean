import RootedKP.RegionalWalkTransfer
import RootedKP.ShortRootEdgeSets

/-! A single regional chart transports canonical edge-set families without
multiplicity. These lemmas separate local geometry from finite root catalogs. -/
namespace RootedKP.Honeycomb
open AKLT
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

namespace LatticeIso

def mapEdges (e : LatticeIso) (edges : Finset Edge) : Finset Edge :=
  edges.image (Sym2.map e.vertex)

lemma map_edge_inverse (e : LatticeIso) (edge : Edge) :
    Sym2.map e.vertex.symm (Sym2.map e.vertex edge) = edge := by
  induction edge using Sym2.inductionOn with
  | hf u v => simp

lemma mapEdges_injective (e : LatticeIso) : Function.Injective e.mapEdges := by
  intro s t h
  have hh := congrArg (Finset.image (Sym2.map e.vertex.symm)) h
  simpa [mapEdges,Finset.image_image,Function.comp_def,e.map_edge_inverse] using hh

lemma traversalEdges_map (e : LatticeIso) (vs : List Vertex) :
    traversalEdges (vs.map e.vertex) = e.mapEdges (traversalEdges vs) := by
  induction vs with
  | nil => simp [traversalEdges,mapEdges]
  | cons u rest ih =>
    cases rest with
    | nil => simp [traversalEdges,mapEdges]
    | cons v rest =>
      simpa only [List.map_cons,traversalEdges,mapEdges,Finset.image_insert,Sym2.map_mk]
        using congrArg (insert s(e.vertex u,e.vertex v)) ih

lemma mapEdges_family_card (e : LatticeIso) (S : Finset (Finset Edge)) :
    (S.image e.mapEdges).card = S.card :=
  Finset.card_image_of_injective S e.mapEdges_injective

end LatticeIso

namespace RegionalChartCover

/-- Literal endpoint-preserving transfer to a chart path. -/
def mapBoundaryPath {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (p : BoundaryPath F 200)
    (hb : ∀ v ∈ p.vertices, VertexWithin center v R) : ShortRootCharts.Path .corner where
  vertices := p.vertices.map c.iso.vertex
  start := c.iso.vertex p.start
  finish := c.iso.vertex p.finish
  head_eq := by simpa using congrArg (Option.map c.iso.vertex) p.head_eq
  last_eq := by simpa using congrArg (Option.map c.iso.vertex) p.last_eq
  start_leaf := (c.leaf_iff (hb p.start (List.mem_of_head? p.head_eq))).mp p.start_leaf
  finish_leaf := (c.leaf_iff (hb p.finish (List.mem_of_getLast? p.last_eq))).mp p.finish_leaf
  distinct := fun h => p.distinct (c.iso.vertex.injective h)
  nodup := p.nodup.map c.iso.vertex.injective
  consecutive := c.listWalk_map p.consecutive hb

@[simp] lemma mapBoundaryPath_length {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (p : BoundaryPath F 200)
    (hb : ∀ v ∈ p.vertices, VertexWithin center v R) :
    (c.mapBoundaryPath p hb).length = p.length := by
  simp [mapBoundaryPath,ShortRootCharts.Path.length,BoundaryPath.length]

@[simp] lemma mapBoundaryPath_edges {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (p : BoundaryPath F 200)
    (hb : ∀ v ∈ p.vertices, VertexWithin center v R) :
    (c.mapBoundaryPath p hb).edges = c.iso.mapEdges (pathEdges p) :=
  c.iso.traversalEdges_map p.vertices

lemma mapBoundaryPath_hits {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (p : BoundaryPath F 200)
    (hb : ∀ v ∈ p.vertices, VertexWithin center v R) (root : Finset Vertex)
    (hit : ∃ v ∈ root, v ∈ p.vertices) :
    ShortRootCharts.hitsRoot (root.image c.iso.vertex) (c.mapBoundaryPath p hb).vertices := by
  obtain ⟨v,hvr,hvp⟩ := hit
  exact ⟨c.iso.vertex v,Finset.mem_image.mpr ⟨v,hvr,rfl⟩,
    List.mem_map.mpr ⟨v,hvp,rfl⟩⟩

/-- A whole family shares one isometry. Its unoriented cardinality is preserved
exactly, and every mapped member remains a literal chart boundary path. -/
theorem path_family_transfer {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (n : ℕ) (root : Finset Vertex)
    (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length=n ∧ pathEdges p=e ∧
      (∀ v ∈ p.vertices, VertexWithin center v R) ∧ (∃ v ∈ root, v ∈ p.vertices)) :
    (S.image c.iso.mapEdges).card = S.card ∧
      ∀ e ∈ S.image c.iso.mapEdges, ∃ p : ShortRootCharts.Path .corner,
        p.length=n ∧ p.edges=e ∧
        ShortRootCharts.hitsRoot (root.image c.iso.vertex) p.vertices := by
  refine ⟨c.iso.mapEdges_family_card S,?_⟩
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨p,hp,rfl,hb,hit⟩ := hS f hf
  exact ⟨c.mapBoundaryPath p hb,by simpa using hp,c.mapBoundaryPath_edges p hb,
    c.mapBoundaryPath_hits p hb root hit⟩

/-- Direct connection to the canonical three-edge corner-root certificate. -/
theorem three_root_family_card_le {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) (n : ℕ) (root : Finset Vertex)
    (hroot : root.image c.iso.vertex = ShortRootCharts.cornerRootThree)
    (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length=n ∧ pathEdges p=e ∧
      (∀ v ∈ p.vertices, VertexWithin center v R) ∧ (∃ v ∈ root, v ∈ p.vertices)) :
    S.card ≤ ShortRootCharts.count ShortRootCharts.cornerRootThree n := by
  obtain ⟨hcard,hpaths⟩ := c.path_family_transfer n root S hS
  rw [← hcard]
  apply ShortRootCharts.edge_family_card_le
  simpa only [hroot] using hpaths

end RegionalChartCover
end
end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.RegionalChartCover.path_family_transfer
#print axioms RootedKP.Honeycomb.RegionalChartCover.three_root_family_card_le
