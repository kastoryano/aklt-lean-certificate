import RootedKP.ThreeRootRegional

namespace RootedKP.Honeycomb

/-- The same face-chart construction works up to radius94. This covers a
root of length41 and every intersecting path of length at most20 at once. -/
theorem regional_chart_cover_large (F : Rectangle) (u : Vertex) (R : ℕ)
    (hu : SunVertex F 200 u) (hR : R≤94) : Nonempty (RegionalChartCover F u R) := by
  obtain ⟨c,hc,huc⟩ := sun_vertex_near_core hu
  obtain ⟨f₀,hf₀,hinc⟩ := hc
  obtain ⟨e,he⟩ := regional_face_chart F 200 (R+5) f₀ hf₀ (by omega)
  refine ⟨⟨e,?_⟩⟩
  intro v hv
  have hcv : VertexWithin c v (R+2) := by
    convert huc.symm.trans hv using 1 <;> omega
  have hfoot : ∀ f, Incident v f → DualWithin f₀ f (R+5) := by
    intro f hf
    exact (incident_dualWithin hinc hf hcv).mono (by omega)
  rw [BoundaryCharts.core_iff]
  constructor
  · rintro ⟨f,hf,hi⟩
    exact ⟨e.face f,(he f (hfoot f hi)).mp hf,(e.incident_iff v f).mpr hi⟩
  · rintro ⟨f,hf,hi⟩
    let g := e.face.symm f
    have hgi : Incident v g := (e.incident_iff v g).mp (by simpa [g] using hi)
    exact ⟨g,(he g (hfoot g hgi)).mpr (by simpa [g] using hf),hgi⟩

end RootedKP.Honeycomb

namespace RootedKP.AKLT
open Honeycomb BoundaryCounts
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- Any root through length41 meets odd short paths in just one common
corner chart. This includes loops and roots with many excursions. -/
theorem odd_small_root_family_count {F : Rectangle} (p : Polymer F) (hp : p.length≤41)
    {n : ℕ} (hn : n≤20) (hodd : n%2=1) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) :
    T.card ≤ cornerCount n := by
  obtain ⟨u,v,l,S,ht,hl,hcore,hcontains⟩ := p.core_trace
  obtain ⟨vs,hhead,hlast,hvslen,hvsset,hwalk⟩ := ht.asList
  have hsun : SunVertex F 200 u := by
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0<(neighbors u).card by rw [neighbors_card]; decide)
    exact ⟨w,(mem_neighbors u w).mp hw,Or.inl (hcore u ht.start_mem)⟩
  obtain ⟨c⟩ := regional_chart_cover_large F u 61 hsun (by decide)
  have hinj : Set.InjOn Polymer.edges (T : Set (Polymer F)) := by
    intro q hq q' hq' he
    exact polymer_eq_of_path_edges q q' (hT q hq).1 (hT q' hq').1 he
  let E := T.image Polymer.edges
  have hE : E.card=T.card := Finset.card_image_of_injOn hinj
  have hfamily : ∀ e ∈ E, ∃ r : BoundaryPath F 200,
      r.length=n ∧ pathEdges r=e ∧ (∀ w ∈ r.vertices,VertexWithin u w 61) ∧
      (∃ w ∈ p.support,w ∈ r.vertices) := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hk,hlen,hinc⟩ := hT q hq
    have hr := q.realization
    rw [hk] at hr
    obtain ⟨r,hr⟩ := hr
    have hrl : r.length=n := (q.length_of_path_realization r hr).symm.trans hlen
    have hrlen : r.vertices.length-1=n := hrl
    obtain ⟨joint,hjp,hjq,hjc⟩ := p.incompatible_core_contact q hinc
    have hjvs : joint ∈ vs := List.mem_toFinset.mp (hvsset.symm ▸ hcontains joint hjp hjc)
    have hqs : q.support=r.vertices.toFinset := by rw [Polymer.support,←hr,path_support_eq]
    have hjr : joint ∈ r.vertices := List.mem_toFinset.mp (hqs ▸ hjq)
    refine ⟨r,hrl,hr,?_,joint,hjp,hjr⟩
    intro w hw
    exact (intersecting_walks_vertexWithin hwalk (listWalk_ambient r.consecutive)
      (List.mem_of_head? hhead) hjvs hjr hw).mono (by omega)
  obtain ⟨hcard,hpaths⟩ := c.path_family_transfer n p.support E hfamily
  rw [← hE,← hcard]
  apply ShortRootCharts.odd_edge_family_card_le n hodd
  intro e he
  obtain ⟨r,hr,hedges,_⟩ := hpaths e he
  exact ⟨r,hr,hedges⟩

end
end RootedKP.AKLT
