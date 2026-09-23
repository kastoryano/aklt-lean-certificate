import RootedKP.ShortRootRegional

namespace RootedKP.AKLT
open Honeycomb ShortRootCharts ShortRootRepresentatives Enumeration BoundaryCounts
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- The six-cycle root has one representative in the finite loop catalog,
valid simultaneously for all incompatible path lengths through twenty. -/
theorem short_loop_root_catalog {F : Rectangle} (p : Polymer F)
    (hk : p.kind=.loop) (hp : p.length≤6) :
    ∃entry∈loopRootTrails,∀n≤20,∀T : Finset (Polymer F),
      (∀q∈T,q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) →
      T.card≤catalogCount entry.2.toFinset n := by
  have hp6 : p.length=6 := by have := p.loop_length_ge_six hk; omega
  have hr := p.realization
  rw [hk] at hr
  change ∃r : SimpleLoop F 200,loopEdges r=p.edges at hr
  obtain ⟨r,hr⟩ := hr
  have hrl : r.length=6 := (p.length_of_loop_realization r hr).symm.trans hp6
  have hrlen : r.vertices.length=6 := hrl
  have hroot : p.support=r.vertices.toFinset := by rw [Polymer.support,←hr,loop_support_eq]
  have hcenter : r.start∈r.vertices := List.mem_of_head? r.head_eq
  have hsun : SunVertex F 200 r.start := ⟨r.finish,sunAdj_symm r.closing⟩
  obtain ⟨c⟩ := regional_chart_cover26 F r.start hsun
  have hrbound : ∀v∈r.vertices,VertexWithin r.start v 26 := by
    intro v hv
    exact (listWalk_vertexWithin (listWalk_ambient r.consecutive) hcenter hv).mono (by omega)
  let vs := r.vertices.map c.iso.vertex
  let anchor := c.iso.vertex r.finish
  have hlast : vs.getLast?=some anchor := by
    simpa [vs,anchor] using congrArg (Option.map c.iso.vertex) r.last_eq
  have hhead : vs.head?=some (c.iso.vertex r.start) := by
    simpa [vs] using congrArg (Option.map c.iso.vertex) r.head_eq
  have hwalk : ListWalk (BoundaryCharts.Adj .corner) vs := c.listWalk_map r.consecutive hrbound
  have hnod : vs.Nodup := r.nodup.map c.iso.vertex.injective
  have hext : Extends (BoundaryCharts.next .corner) 5 [anchor] vs := by
    have hh := chart_walk_to_extends .corner hlast hnod hwalk
    simpa [vs,hrlen] using hh
  have hclosing : BoundaryCharts.Adj .corner anchor (c.iso.vertex r.start) := by
    exact (c.adjacency_iff (hrbound r.finish (List.mem_of_getLast? r.last_eq)) r.start).mp r.closing
  have hend : endsAt (fun v => BoundaryCharts.Adj .corner v anchor) vs := by
    cases hv : vs with
    | nil => simp [hv] at hhead
    | cons v rest =>
      have heq : v=c.iso.vertex r.start := by simpa [hv] using hhead
      exact heq ▸ BoundaryCharts.adj_symm hclosing
  refine ⟨(normalize anchor anchor,vs.map (normalize anchor)),loop_root_representative hext hend,?_⟩
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
  obtain ⟨hq,hr⟩ := adjacent_anchor_bounds hclosing
  apply chart_edge_family_catalog_count (show 5≤6 by omega) hn hq hr hext
  have heqs : p.support.image c.iso.vertex=vs.toFinset := by
    rw [hroot]
    ext v
    simp [vs]
  simpa only [heqs] using hpaths

end
end RootedKP.AKLT
