import RootedKP.OddChartCounts
import RootedKP.RegionalChartPolymers
import RootedKP.PolymerRingCover
import RootedKP.PathTailEdges

namespace RootedKP.ShortRootCharts
open Honeycomb BoundaryCharts BoundaryCounts AKLT
set_option maxHeartbeats 0

theorem corner_paths_three_exact : cornerPaths 3 =
    {[Vertex.b (-2) 0,Vertex.a (-1) 0,Vertex.b (-1) 0,Vertex.a (-1) 1]} := by
  decide +kernel

/-- A three-edge chart path is the literal corner root, independently of
where its traversal was initially anchored and which direction was chosen. -/
theorem Path.three_support (p : Path .corner) (hp : p.length=3) :
    p.vertices.toFinset = cornerRootThree := by
  obtain ⟨trail,ht,he⟩ := p.odd_encoding (by omega)
  rw [hp,corner_paths_three_exact,Finset.mem_singleton] at ht
  subst trail
  have hl : 2≤p.vertices.length := by unfold Path.length at hp; omega
  change traversalEdges _ = traversalEdges p.vertices at he
  rw [← traversal_support_eq hl,← he]
  decide +kernel

end RootedKP.ShortRootCharts

namespace RootedKP.AKLT
open Honeycomb
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- Every finite length-n path family incompatible with an actual length-three
root embeds in the one certified W3 corner family. The map is shared by the
entire family, and preserves unoriented edge sets injectively. -/
theorem three_root_family_count {F : Rectangle} (p : Polymer F) (hp : p.length=3)
    {n : ℕ} (hn : n≤20) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) :
    T.card ≤ ShortRootCharts.count ShortRootCharts.cornerRootThree n := by
  have hk : p.kind=.path := by
    cases he : p.kind with
    | path => rfl
    | loop => have hh := p.loop_length_ge_six he; omega
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨r,hr⟩ := hr
  have hrl : r.length=3 := (p.length_of_path_realization r hr).symm.trans hp
  have hrlen : r.vertices.length-1=3 := hrl
  have hroot : p.support=r.vertices.toFinset := by rw [Polymer.support,←hr,path_support_eq]
  have hcenter : r.start ∈ r.vertices := List.mem_of_head? r.head_eq
  have hsun : SunVertex F 200 r.start := by
    refine ⟨r.vertex 1,?_⟩
    have hh := r.at_adjacent 0 (by omega)
    rw [r.at_start] at hh
    exact hh
  obtain ⟨c⟩ := regional_chart_cover26 F r.start hsun
  have hrbound : ∀ v ∈ r.vertices, VertexWithin r.start v 26 := by
    intro v hv
    exact (listWalk_vertexWithin (listWalk_ambient r.consecutive) hcenter hv).mono (by omega)
  have hmroot : p.support.image c.iso.vertex = ShortRootCharts.cornerRootThree := by
    have hh := (c.mapBoundaryPath r hrbound).three_support (by simpa [RegionalChartCover.mapBoundaryPath,ShortRootCharts.Path.length,BoundaryPath.length] using hrl)
    rw [hroot]
    convert hh using 1
    ext v
    simp [RegionalChartCover.mapBoundaryPath]
  have hinj : Set.InjOn Polymer.edges (T : Set (Polymer F)) := by
    intro q hq q' hq' he
    exact polymer_eq_of_path_edges q q' (hT q hq).1 (hT q' hq').1 he
  rw [← Finset.card_image_of_injOn hinj]
  apply c.three_root_family_card_le n p.support hmroot
  intro e he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hqk,hqn,hinc⟩ := hT q hq
  have hqr := q.realization
  rw [hqk] at hqr
  obtain ⟨s,hs⟩ := hqr
  have hsl : s.length=n := (q.length_of_path_realization s hs).symm.trans hqn
  have hslen : s.vertices.length-1=n := hsl
  have hqs : q.support=s.vertices.toFinset := by rw [Polymer.support,←hs,path_support_eq]
  obtain ⟨joint,hjp,hjq⟩ := Finset.not_disjoint_iff.mp hinc
  have hjr : joint ∈ r.vertices := List.mem_toFinset.mp (hroot ▸ hjp)
  have hjs : joint ∈ s.vertices := List.mem_toFinset.mp (hqs ▸ hjq)
  refine ⟨s,hsl,hs,?_,joint,hjp,hjs⟩
  intro v hv
  exact (intersecting_walks_vertexWithin (listWalk_ambient r.consecutive)
    (listWalk_ambient s.consecutive) hcenter hjr hjs hv).mono (by omega)

end
end RootedKP.AKLT
