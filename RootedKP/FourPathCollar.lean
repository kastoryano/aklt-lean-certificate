import RootedKP.ZeroCollarImage
import RootedKP.TrimmedRootTrace
import RootedKP.RegionalLoopCounting
namespace RootedKP.AKLT
open Honeycomb Honeycomb.BoundaryLeaves
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
theorem Polymer.four_rightEndpoint_contact {F : Rectangle} (q : Polymer F)
    (hq : q.kind=.path) (hn : q.length=4)
    {v : Vertex} (hv : v∈q.support) (hc : Core F 200 v) :
    CircleArcs.Near (BoundaryCycle.perimeter F 0) 2
      (imageIndex F 0 v) (imageCoordinate F 0 q.rightEndpoint) := by
  obtain ⟨hcan,r,hr,t,ht,hts,hends⟩ := q.rightEndpoint_spec hq (by omega) (by omega)
  have hlen : q.length=r.length := q.length_of_path_realization r hr
  have hsupport : q.support=r.vertices.toFinset := by
    rw [Polymer.support,←hr,path_support_eq]
  rw [hsupport,List.mem_toFinset] at hv
  obtain ⟨j,hj,hjv⟩ := List.mem_iff_getElem.mp hv
  have heq : r.vertex j=v := by simp only [BoundaryPath.vertex,List.getD_eq_getElem _ _ hj,hjv]
  have hin : j≤r.length := by have := r.vertices_length; omega
  have hj0 : 0 < j := by
    by_contra hh
    exact Honeycomb.leaf_not_core r.start_leaf
      (by simpa [←heq,show j=0 by omega,r.at_start] using hc)
  have hj1 : j < r.length := by
    by_contra hh
    exact Honeycomb.leaf_not_core r.finish_leaf
      (by simpa [←heq,show j=r.length by omega,r.at_finish] using hc)
  rcases hends with hends | hends
  · have hh := ZeroCollar.fixed_collar_image_near r (d:=0) (by omega) (by omega) (by omega)
      hj0 hj1 (show 0 < r.length-1 by omega) (show r.length-1 < r.length by omega)
    rw [path_finish_attachment r (candidate_valid hcan) hends.2] at hh
    have hh' := hh.mod_right (attachment_image_coordinate (by omega) (candidate_valid hcan))
    simpa [heq,←hlen,hn] using hh'
  · have hh := ZeroCollar.fixed_collar_image_near r (d:=0) (by omega) (by omega) (by omega)
      hj0 hj1 (show 0 < 1 by omega) (show 1 < r.length by omega)
    rw [path_start_attachment r (candidate_valid hcan) hends.2] at hh
    have hh' := hh.mod_right (attachment_image_coordinate (by omega) (candidate_valid hcan))
    simpa [heq,←hlen,hn] using hh'

theorem four_piece_endpoint_count {F : Rectangle}
    (piece : TracePiece (Ring F 0)) (T : Finset (Polymer F))
    (hT : ∀q∈T,q.kind=.path ∧ q.length=4 ∧ ¬Disjoint piece.support q.support) :
    2*(T.image Polymer.rightEndpoint).card≤piece.length+6 := by
  obtain ⟨vs,hh,hl,hlen,hset,hw⟩ := piece.trace.asList
  apply candidates_near_trace F (d:=0) (n:=4) (by omega) (by omega)
    (vs.map (imageIndex F 0))
  · exact ZeroCollar.ring_image_trace (by omega) (by omega) hw
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
    refine ⟨imageIndex F 0 v,?_,?_⟩
    · exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp (by rw [hset]; exact hvp),rfl⟩
    · exact q.four_rightEndpoint_contact hk hn hvq (piece.in_region v hvp).1

theorem four_root_family_count {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    (T : Finset (Polymer F))
    (hT : ∀q∈T,q.kind=.path ∧ q.length=4 ∧ Polymer.Incompatible p q) :
    2*T.card≤p.traceLength+6 := by
  obtain ⟨parts,hbudget,hcover⟩ := p.ring_cover_trimmed (d:=0) (K:=6) (by omega) (by omega)
  let f : TracePiece (Ring F 0) → Finset (Fin 6 × ℤ) := fun piece =>
    (T.filter (fun q => ¬Disjoint piece.support q.support)).image Polymer.rightEndpoint
  have hcov : ∀ a∈T.image Polymer.rightEndpoint,∃piece∈parts,a∈f piece := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hk,hn,hi⟩ := hT q hq
    obtain ⟨piece,hpiece,hmeet⟩ := hcover q hi
      (q.path_support_avoids_deeper_core hk (by omega) (by omega))
    exact ⟨piece,hpiece,Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hmeet⟩,rfl⟩⟩
  have hc := card_le_list_sum_of_cover _ parts f hcov
  have hpart : ∀piece,2*(f piece).card≤piece.length+6 := by
    intro piece
    apply four_piece_endpoint_count
    intro q hq
    obtain ⟨hqT,hmeet⟩ := Finset.mem_filter.mp hq
    exact ⟨(hT q hqT).1,(hT q hqT).2.1,hmeet⟩
  have hsum : 2*(parts.map (fun piece => (f piece).card)).sum≤
      (parts.map TracePiece.length).sum+6*parts.length := by
    clear hc hcov hcover hbudget
    induction parts with
    | nil => simp
    | cons piece rest ih =>
      have hp := hpart piece
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add hp ih
  have hends := (Nat.mul_le_mul_left 2 hc).trans (hsum.trans hbudget)
  have ht := family_card_le_endpoint_card_mul (show 4≤20 by omega) (show 4%2=0 by omega)
    T (fun q hq => ⟨(hT q hq).1,(hT q hq).2.1⟩)
  rw [BoundaryCounts.sideCount_four] at ht
  omega


theorem four_root_count_relaxed {F : Rectangle} (p : Polymer F) (hp : 7≤p.length) :
    5*pathLengthCount p 1≤4*p.length := by
  have hh := four_root_family_count p hp
    ((shortPathSet p).filter (fun q => q.length=4)) (counted_path_spec p 1)
  change 2*pathLengthCount p 1≤p.traceLength+6 at hh
  cases hk : p.kind with
  | path =>
    simp only [Polymer.traceLength,hk,ite_true] at hh
    omega
  | loop =>
    have hmin : 10≤p.length := by
      rcases p.loop_length_eq_six_or_ge_ten hk with h | h
      · omega
      · exact h
    simp only [Polymer.traceLength,hk,show Kind.loop≠Kind.path by decide,ite_false] at hh
    omega

end
end RootedKP.AKLT
