import RootedKP.PolymerRingCover
import RootedKP.RingImageTrace

namespace RootedKP.AKLT
open Honeycomb Honeycomb.BoundaryLeaves
noncomputable section
open scoped Classical
set_option maxHeartbeats 0

namespace Polymer
variable {F : Rectangle}

/-- The larger of the two actual leaf parameters on their common side.
The definition mentions only a realization of the canonical edge set. -/
def RightEndpoint (p : Polymer F) (a : Fin 6 × ℤ) : Prop :=
  Candidate F a.1 a.2 ∧ ∃r : BoundaryPath F 200, pathEdges r=p.edges ∧
    ∃t : ℤ, Valid F a.1 t ∧ t<a.2 ∧
      ((r.start=leaf F a.1 t ∧ r.finish=leaf F a.1 a.2) ∨
       (r.finish=leaf F a.1 t ∧ r.start=leaf F a.1 a.2))

lemma exists_rightEndpoint (p : Polymer F) (hk : p.kind=.path)
    (hmax : p.length≤20) (heven : p.length%2=0) : ∃a,p.RightEndpoint a := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨r,hr⟩ := hr
  have hlen : p.length=r.length := p.length_of_path_realization r hr
  obtain ⟨i,t,s,ht,hs,hts,hends⟩ := oriented_endpoints r (hlen ▸ hmax) (hlen ▸ heven)
  exact ⟨(i,s),hs,r,hr,t,ht,hts,hends⟩

/-- Choice selects one endpoint per edge-set polymer, never one per traversal. -/
def rightEndpoint (p : Polymer F) : Fin 6 × ℤ :=
  if h : ∃a,p.RightEndpoint a then h.choose else (0,0)

lemma rightEndpoint_spec (p : Polymer F) (hk : p.kind=.path)
    (hmax : p.length≤20) (heven : p.length%2=0) : p.RightEndpoint p.rightEndpoint := by
  have hh := p.exists_rightEndpoint hk hmax heven
  simp only [rightEndpoint,dif_pos hh]
  exact hh.choose_spec

lemma rightEndpoint_contact (q : Polymer F) (hq : q.kind=.path)
    (hmin : 8≤q.length) (hmax : q.length≤20) (heven : q.length%2=0)
    {v : Vertex} (hv : v∈q.support) (hc : Core F 200 v) :
    CircleArcs.Near (BoundaryCycle.perimeter F (q.length/4-1)) (q.length-2 : ℕ)
      (imageIndex F (q.length/4-1) v)
      (imageCoordinate F (q.length/4-1) q.rightEndpoint) := by
  obtain ⟨hcan,r,hr,t,ht,hts,hends⟩ := q.rightEndpoint_spec hq hmax heven
  have hlen : q.length=r.length := q.length_of_path_realization r hr
  have hsupport : q.support=r.vertices.toFinset := by rw [support,←hr,path_support_eq]
  rw [hsupport,List.mem_toFinset] at hv
  obtain ⟨j,hj,hjv⟩ := List.mem_iff_getElem.mp hv
  have heq : r.vertex j=v := by simp only [BoundaryPath.vertex,List.getD_eq_getElem _ _ hj,hjv]
  have hin : j≤r.length := by have := r.vertices_length; omega
  have hj0 : 0 < j := by
    by_contra hh
    have hz : j=0 := by omega
    exact Honeycomb.leaf_not_core r.start_leaf (by simpa [←heq,hz,r.at_start] using hc)
  have hj1 : j < r.length := by
    by_contra hh
    have hz : j=r.length := by omega
    exact Honeycomb.leaf_not_core r.finish_leaf (by simpa [←heq,hz,r.at_finish] using hc)
  rcases hends with hends | hends
  · have hh := short_path_endpoint_contact r (by omega) (by omega) (by omega) hj0 hj1
      (candidate_valid hcan) hends.2
    simpa only [heq,←hlen,Prod.eta] using hh
  · have hh := short_path_start_contact r (by omega) (by omega) (by omega) hj0 hj1
      (candidate_valid hcan) hends.2
    simpa only [heq,←hlen,Prod.eta] using hh

/-- A finite family of actual short even paths touching one retained root
piece has at most half the padded piece length in distinct right endpoints. -/
theorem piece_endpoint_count {n : ℕ} (hmin : 8≤n) (hmax : n≤20) (heven : n%2=0)
    (piece : TracePiece (Ring F (n/4-1))) (T : Finset (Polymer F))
    (hT : ∀q∈T,q.kind=.path ∧ q.length=n ∧ ¬Disjoint piece.support q.support) :
    2*(T.image rightEndpoint).card≤piece.length+2*(n-1+6*(n/4-1)) := by
  obtain ⟨vs,hh,hl,hlen,hset,hw⟩ := piece.trace.asList
  apply candidates_near_trace F (by omega) (by omega) (vs.map (imageIndex F (n/4-1)))
  · exact ring_image_trace (by omega) (by omega) hw
      (fun v hv => piece.in_region v (by rw [←hset]; exact List.mem_toFinset.mpr hv))
  · simpa [hlen]
  · intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hk,hn,_⟩ := hT q hq
    exact (q.rightEndpoint_spec hk (by omega) (by omega)).1
  · intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hk,hn,hcontact⟩ := hT q hq
    obtain ⟨v,hvp,hvq⟩ := Finset.not_disjoint_iff.mp hcontact
    refine ⟨imageIndex F (n/4-1) v,?_,?_⟩
    · apply List.mem_map.mpr
      exact ⟨v,List.mem_toFinset.mp (by rw [hset]; exact hvp),rfl⟩
    · simpa only [hn] using q.rightEndpoint_contact hk (by omega) (by omega)
        (by omega) hvq (piece.in_region v hvp).1

end Polymer
end
end RootedKP.AKLT
