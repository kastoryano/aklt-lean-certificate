import RootedKP.OddRegionalCounts
import RootedKP.BoundaryLeaves

namespace RootedKP.Honeycomb
open AKLT BoundaryCharts
noncomputable section
open scoped Classical
set_option maxHeartbeats 0

theorem cornerIso_core {F : Rectangle} (i : Fin 6) {v : Vertex} (hv : Core F 200 v) :
    BoundaryCharts.core .corner ((cornerIso F 200 i).vertex v) := by
  obtain ⟨f,hf,hinc⟩ := hv
  apply (core_iff _ _).mpr
  exact ⟨(cornerIso F 200 i).face f,
    (cornerIso_face_iff F 200 i f).mpr ⟨sideMargin_nonnegative hf i,
      sideMargin_nonnegative hf (chartNextSide i)⟩,
    ((cornerIso F 200 i).incident_iff v f).mpr hinc⟩

theorem cornerIso_sunAdj {F : Rectangle} (i : Fin 6) {u v : Vertex} (h : SunAdj F 200 u v) :
    BoundaryCharts.Adj .corner ((cornerIso F 200 i).vertex u) ((cornerIso F 200 i).vertex v) := by
  exact ⟨((cornerIso F 200 i).adj_iff u v).mpr h.1,
    h.2.elim (fun hu => Or.inl (cornerIso_core i hu)) (fun hv => Or.inr (cornerIso_core i hv))⟩

theorem cornerIso_side_leaf {F : Rectangle} (i : Fin 6) {r : ℤ}
    (hr : BoundaryLeaves.Valid F i r) :
    BoundaryCharts.Leaf .corner ((cornerIso F 200 i).vertex (BoundaryLeaves.leaf F i r)) := by
  apply (leafCode_iff _ _).mp
  have hq := F.q_order
  have hR := F.r_order
  fin_cases i <;>
    simp [cornerIso,LatticeIso.rotateN,LatticeIso.comp,LatticeIso.identity,LatticeIso.rotation,
      LatticeIso.translation,translate,BoundaryLeaves.leaf,fromChart,sideChart,rotate,
      leafCode,upperLeaf,leftLeaf,BoundaryLeaves.Valid] at hr ⊢ <;> omega

theorem cornerIso_next_leaf {F : Rectangle} (i : Fin 6) {r : ℤ}
    (hr : BoundaryLeaves.Valid F (chartNextSide i) r) :
    BoundaryCharts.Leaf .corner
      ((cornerIso F 200 i).vertex (BoundaryLeaves.leaf F (chartNextSide i) r)) := by
  apply (leafCode_iff _ _).mp
  have hq := F.q_order
  have hR := F.r_order
  fin_cases i <;>
    simp [cornerIso,LatticeIso.rotateN,LatticeIso.comp,LatticeIso.identity,LatticeIso.rotation,
      LatticeIso.translation,translate,BoundaryLeaves.leaf,fromChart,sideChart,rotate,
      chartNextSide,leafCode,upperLeaf,leftLeaf,BoundaryLeaves.Valid] at hr ⊢ <;> omega

theorem short_odd_adjacent_sides {F : Rectangle} {i j : Fin 6} {r s : ℤ} {n : ℕ}
    (hi : BoundaryLeaves.Valid F i r) (hj : BoundaryLeaves.Valid F j s)
    (hw : Walk (BoundaryLeaves.leaf F i r) (BoundaryLeaves.leaf F j s) n)
    (hn : n≤20) (hodd : n%2=1) : j=chartNextSide i ∨ i=chartNextSide j := by
  have hq := hw.height_bounds heightQ_lipschitz
  have hr := hw.height_bounds heightR_lipschitz
  have hs := hw.height_bounds heightS_lipschitz
  have hp := hw.heightQ_parity
  have hFq := F.q_order
  have hFr := F.r_order
  fin_cases i <;> fin_cases j <;>
    simp [chartNextSide,BoundaryLeaves.Valid,BoundaryLeaves.leaf,sideChart,fromChart,
      rotate,heightQ,heightR,heightS] at hi hj hq hr hs hp ⊢ <;> omega

def cornerPath {F : Rectangle} (p : BoundaryPath F 200) (i : Fin 6)
    (hs : BoundaryCharts.Leaf .corner ((cornerIso F 200 i).vertex p.start))
    (hf : BoundaryCharts.Leaf .corner ((cornerIso F 200 i).vertex p.finish)) :
    ShortRootCharts.Path .corner where
  vertices := p.vertices.map (cornerIso F 200 i).vertex
  start := (cornerIso F 200 i).vertex p.start
  finish := (cornerIso F 200 i).vertex p.finish
  head_eq := by simpa using congrArg (Option.map (cornerIso F 200 i).vertex) p.head_eq
  last_eq := by simpa using congrArg (Option.map (cornerIso F 200 i).vertex) p.last_eq
  start_leaf := hs
  finish_leaf := hf
  distinct := fun h => p.distinct ((cornerIso F 200 i).vertex.injective h)
  nodup := p.nodup.map (cornerIso F 200 i).vertex.injective
  consecutive := AKLT.listWalk_map (cornerIso F 200 i).vertex (fun _ _ h => cornerIso_sunAdj i h) p.consecutive

theorem odd_path_corner_encoding {F : Rectangle} (p : BoundaryPath F 200)
    (hn : p.length≤20) (hodd : p.length%2=1) :
    ∃ i : Fin 6, ∃ q : ShortRootCharts.Path .corner,
      q.length=p.length ∧ q.edges=(cornerIso F 200 i).mapEdges (pathEdges p) := by
  obtain ⟨i,r,hr,hs⟩ := BoundaryLeaves.leaf_coverage p.start_leaf
  obtain ⟨j,s,hs',hf⟩ := BoundaryLeaves.leaf_coverage p.finish_leaf
  have hw : Walk p.start p.finish p.length := by
    have hh := indexed_subwalk (fun k hk => (p.at_adjacent k hk).1) 0 p.length (by omega)
    simpa only [Nat.zero_add,p.at_start,p.at_finish] using hh
  rw [hs,hf] at hw
  have henc : ∀ k : Fin 6,
      BoundaryCharts.Leaf .corner ((cornerIso F 200 k).vertex p.start) →
      BoundaryCharts.Leaf .corner ((cornerIso F 200 k).vertex p.finish) →
      ∃ q : ShortRootCharts.Path .corner,
        q.length=p.length ∧ q.edges=(cornerIso F 200 k).mapEdges (pathEdges p) := by
    intro k hstart hfinish
    refine ⟨cornerPath p k hstart hfinish,?_,?_⟩
    · simp [cornerPath,ShortRootCharts.Path.length,BoundaryPath.length]
    · exact (cornerIso F 200 k).traversalEdges_map p.vertices
  rcases short_odd_adjacent_sides hr hs' hw hn hodd with rfl | hji
  · refine ⟨i,?_⟩
    apply henc i
    · rw [hs]; exact cornerIso_side_leaf i hr
    · rw [hf]; exact cornerIso_next_leaf i hs'
  · subst i
    refine ⟨j,?_⟩
    apply henc j
    · rw [hs]; exact cornerIso_next_leaf j hr
    · rw [hf]; exact cornerIso_side_leaf j hs'

end
end RootedKP.Honeycomb

namespace RootedKP.AKLT
open Honeycomb BoundaryCounts
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

/-- All odd short regional paths belong to six globally embedded corner
families. The inequality counts canonical unoriented edge sets. -/
theorem global_odd_family_count {F : Rectangle} {n : ℕ} (hn : n≤20) (hodd : n%2=1)
    (T : Finset (Polymer F)) (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n) :
    T.card ≤ 6*cornerCount n := by
  let f : Fin 6 → Finset (Polymer F) := fun i => T.filter (fun q =>
    ∃ r : ShortRootCharts.Path .corner,
      r.length=n ∧ r.edges=(cornerIso F 200 i).mapEdges q.edges)
  have hcover : T ⊆ Finset.univ.biUnion f := by
    intro q hq
    obtain ⟨hk,hlen⟩ := hT q hq
    have hr := q.realization
    rw [hk] at hr
    change ∃ p : BoundaryPath F 200, pathEdges p=q.edges at hr
    obtain ⟨p,hp⟩ := hr
    have hpl : p.length=n := (q.length_of_path_realization p hp).symm.trans hlen
    obtain ⟨i,r,hr,he⟩ := odd_path_corner_encoding p (hpl.symm ▸ hn) (hpl.symm ▸ hodd)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
      ⟨hq,r,hr.trans hpl,he.trans (congrArg (cornerIso F 200 i).mapEdges hp)⟩⟩
  have hbound : ∀ i, (f i).card ≤ cornerCount n := by
    intro i
    let g := fun q : Polymer F => (cornerIso F 200 i).mapEdges q.edges
    have hi : Set.InjOn g (f i : Set (Polymer F)) := by
      intro q hq q' hq' he
      exact polymer_eq_of_path_edges q q' (hT q (Finset.mem_filter.mp hq).1).1
        (hT q' (Finset.mem_filter.mp hq').1).1
        ((cornerIso F 200 i).mapEdges_injective he)
    rw [← Finset.card_image_of_injOn hi]
    apply ShortRootCharts.odd_edge_family_card_le n hodd
    intro e he
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hq).2
  calc
    T.card ≤ (Finset.univ.biUnion f).card := Finset.card_le_card hcover
    _ ≤ ∑ i : Fin 6, (f i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 6, cornerCount n := Finset.sum_le_sum (fun i _ => hbound i)
    _ = 6*cornerCount n := by simp

end
end RootedKP.AKLT
