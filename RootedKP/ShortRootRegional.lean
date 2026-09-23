import RootedKP.ShortRootReduction
import RootedKP.ThreeRootRegional

namespace RootedKP.ShortRootRepresentatives
open Honeycomb BoundaryCharts BoundaryCounts Enumeration ShortRootCharts AKLT
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem chart_edge_family_catalog_count {ell n : ℕ} (hell : ell≤6) (hn : n≤20)
    {anchor : Vertex} {root : List Vertex}
    (hqa : -2≤qCoord anchor) (hra : rCoord anchor≤1)
    (hroot : Extends (next .corner) ell [anchor] root)
    (S : Finset (Finset Edge))
    (hS : ∀ e∈S,∃p : Path .corner,p.length=n ∧ p.edges=e ∧ hitsRoot root.toFinset p.vertices) :
    S.card≤catalogCount (root.map (normalize anchor)).toFinset n := by
  have hex : ∀e : S,∃trail,Traversal root.toFinset n trail ∧ traversalEdges trail=e.val := by
    intro e
    obtain ⟨p,hp,he,hit⟩ := hS e.val e.property
    obtain ⟨trail,ht,het⟩ := p.ordered_encoding root.toFinset hit
    exact ⟨trail,hp ▸ ht,het.trans he⟩
  choose f hf hfe using hex
  let U := Finset.univ.image f
  have hinj : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    exact (hfe e).symm.trans ((congrArg traversalEdges he).trans (hfe e'))
  have hc : U.card=S.card := by simp [U,Finset.card_image_of_injective _ hinj]
  rw [←hc]
  apply short_root_count_le hell hn hqa hra hroot U
  intro trail ht
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp ht
  exact hf e

end
end RootedKP.ShortRootRepresentatives

namespace RootedKP.AKLT
open Honeycomb ShortRootCharts ShortRootRepresentatives Enumeration
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- One catalog representative controls every length up to twenty, for every
actual family incompatible with this regional short path root. -/
theorem short_path_root_catalog {F : Rectangle} (p : Polymer F)
    (hk : p.kind=.path) (hp : p.length≤6) :
    ∃root∈boundaryRootTrails p.length,∀n≤20,∀T : Finset (Polymer F),
      (∀q∈T,q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) →
      T.card≤catalogCount root.toFinset n := by
  have hr := p.realization
  rw [hk] at hr
  change ∃r : BoundaryPath F 200,pathEdges r=p.edges at hr
  obtain ⟨r,hr⟩ := hr
  have hrl : r.length=p.length := (p.length_of_path_realization r hr).symm
  have hrlen : r.vertices.length-1=p.length := hrl
  have hmin := p.length_ge_three
  have hroot : p.support=r.vertices.toFinset := by rw [Polymer.support,←hr,path_support_eq]
  have hcenter : r.start∈r.vertices := List.mem_of_head? r.head_eq
  have hsun : SunVertex F 200 r.start := by
    refine ⟨r.vertex 1,?_⟩
    have hh := r.at_adjacent 0 (by omega)
    rw [r.at_start] at hh
    exact hh
  obtain ⟨c⟩ := regional_chart_cover26 F r.start hsun
  have hrbound : ∀v∈r.vertices,VertexWithin r.start v 26 := by
    intro v hv
    exact (listWalk_vertexWithin (listWalk_ambient r.consecutive) hcenter hv).mono (by omega)
  let rp := c.mapBoundaryPath r hrbound
  have hrplen : rp.length=p.length := by simpa [rp] using hrl
  have hext : Extends (BoundaryCharts.next .corner) p.length [rp.finish] rp.vertices := by
    rw [←hrplen]
    exact chart_walk_to_extends .corner rp.last_eq rp.nodup rp.consecutive
  have hend : BoundaryCounts.endsAt (BoundaryCharts.Leaf .corner) rp.vertices := by
    have hh := rp.head_eq
    cases hv : rp.vertices with
    | nil => simp [hv] at hh
    | cons v vs =>
      have heq : v=rp.start := by simpa [hv] using hh
      exact heq ▸ rp.start_leaf
  refine ⟨rp.vertices.map (normalize rp.finish),
    boundary_root_representative hp hext rp.finish_leaf hend,?_⟩
  intro n hn T hT
  have hinj : Set.InjOn Polymer.edges (T : Set (Polymer F)) := by
    intro q hq q' hq' he
    exact polymer_eq_of_path_edges q q' (hT q hq).1 (hT q' hq').1 he
  rw [←Finset.card_image_of_injOn hinj]
  have hfamily : ∀e∈T.image Polymer.edges,∃s : BoundaryPath F 200,
      s.length=n ∧ pathEdges s=e ∧ (∀v∈s.vertices,VertexWithin r.start v 26) ∧
      (∃v∈p.support,v∈s.vertices) := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hqk,hqn,hinc⟩ := hT q hq
    have hqr := q.realization
    rw [hqk] at hqr
    change ∃s : BoundaryPath F 200,pathEdges s=q.edges at hqr
    obtain ⟨s,hs⟩ := hqr
    have hsl : s.length=n := (q.length_of_path_realization s hs).symm.trans hqn
    have hslen : s.vertices.length-1=n := hsl
    have hqs : q.support=s.vertices.toFinset := by rw [Polymer.support,←hs,path_support_eq]
    obtain ⟨joint,hjp,hjq⟩ := Finset.not_disjoint_iff.mp hinc
    have hjr : joint∈r.vertices := List.mem_toFinset.mp (hroot ▸ hjp)
    have hjs : joint∈s.vertices := List.mem_toFinset.mp (hqs ▸ hjq)
    refine ⟨s,hsl,hs,?_,joint,hjp,hjs⟩
    intro v hv
    exact (intersecting_walks_vertexWithin (listWalk_ambient r.consecutive)
      (listWalk_ambient s.consecutive) hcenter hjr hjs hv).mono (by omega)
  obtain ⟨hc,hpaths⟩ := c.path_family_transfer n p.support (T.image Polymer.edges) hfamily
  rw [←hc]
  obtain ⟨hq,hr⟩ := leaf_anchor_bounds rp.finish_leaf
  apply chart_edge_family_catalog_count hp hn hq hr hext
  have heqs : p.support.image c.iso.vertex=rp.vertices.toFinset := by
    rw [hroot]
    ext v
    simp [rp,RegionalChartCover.mapBoundaryPath]
  simpa only [heqs] using hpaths

end
end RootedKP.AKLT
