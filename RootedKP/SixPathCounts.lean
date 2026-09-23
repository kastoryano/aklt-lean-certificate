import RootedKP.CompletedLengthCounts

/-! The exceptional length-six count follows from the same collar machinery,
using the fixed width one collar. Integrality absorbs the last half-unit. -/
namespace RootedKP.Honeycomb
open BoundaryCycle CircleArcs
noncomputable section
set_option maxHeartbeats 0

theorem fixed_collar_image_near {F : Rectangle} (p : BoundaryPath F 200)
    {d : ℕ} (hd0 : 1≤d) (hd1 : d≤4)
    (hshort : p.length≤4*(d+1)+2)
    {i j : ℕ} (hi0 : 0 < i) (hi1 : i < p.length) (hj0 : 0 < j) (hj1 : j < p.length) :
    Near (perimeter F d) (p.length-2 : ℕ)
      (imageIndex F d (p.vertex i)) (imageIndex F d (p.vertex j)) := by
  have hlen := RootedKP.AKLT.boundaryPath_length_ge_three p
  have hinner : ∀ k, 0 < k → k < p.length → InnerBoundary F d (collarMap F d (p.vertex k)) := by
    intro k hk0 hk1
    apply collarMap_image_inner hd1
    by_cases hk : k+1 < p.length
    · obtain ⟨s,hs,_⟩ := collar_edge_cell_cover hd0 hd1
        (p.trimmed_edge_in_collar (by omega) hshort hk0 hk)
      exact ⟨s,hs⟩
    · obtain ⟨s,_,hs⟩ := collar_edge_cell_cover hd0 hd1
        (p.trimmed_edge_in_collar (by omega) hshort (by omega : 0 < k-1) (by omega))
      exact ⟨s,by simpa [show k-1+1=k by omega] using hs⟩
  let f : ℕ → ℤ := fun k => imageIndex F d (p.vertex (k+1))
  have hs : ∀ k < p.length-2, Near (perimeter F d) 1 (f k) (f (k+1)) := by
    intro k hk
    apply innerIndex_near_weak hd1 (hinner _ (by omega) (by omega))
      (hinner _ (by omega) (by omega))
    exact collarMap_contracts_actual_edge hd0 hd1
      (p.trimmed_edge_in_collar (by omega) hshort (by omega) (by omega))
  by_cases hij : i≤j
  · have hh := indexed_near hs (i-1) (j-i) (by omega)
    simpa only [f,show i-1+1=i by omega,show i-1+(j-i)+1=j by omega]
      using hh.mono (by omega)
  · have hh := indexed_near hs (j-1) (i-j) (by omega)
    simpa only [f,show j-1+1=j by omega,show j-1+(i-j)+1=i by omega]
      using hh.symm.mono (by omega)

end
end RootedKP.Honeycomb

namespace RootedKP.AKLT
open Honeycomb Honeycomb.BoundaryLeaves
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem Polymer.six_rightEndpoint_contact {F : Rectangle} (q : Polymer F)
    (hq : q.kind=.path) (hn : q.length=6)
    {v : Vertex} (hv : v∈q.support) (hc : Core F 200 v) :
    CircleArcs.Near (BoundaryCycle.perimeter F 1) 4
      (imageIndex F 1 v) (imageCoordinate F 1 q.rightEndpoint) := by
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
  · have hh := fixed_collar_image_near r (d:=1) (by omega) (by omega) (by omega)
      hj0 hj1 (show 0 < r.length-1 by omega) (show r.length-1 < r.length by omega)
    rw [path_finish_attachment r (candidate_valid hcan) hends.2] at hh
    have hh' := hh.mod_right (attachment_image_coordinate (by omega) (candidate_valid hcan))
    simpa [heq,←hlen,hn] using hh'
  · have hh := fixed_collar_image_near r (d:=1) (by omega) (by omega) (by omega)
      hj0 hj1 (show 0 < 1 by omega) (show 1 < r.length by omega)
    rw [path_start_attachment r (candidate_valid hcan) hends.2] at hh
    have hh' := hh.mod_right (attachment_image_coordinate (by omega) (candidate_valid hcan))
    simpa [heq,←hlen,hn] using hh'

theorem six_piece_endpoint_count {F : Rectangle}
    (piece : TracePiece (Ring F 1)) (T : Finset (Polymer F))
    (hT : ∀q∈T,q.kind=.path ∧ q.length=6 ∧ ¬Disjoint piece.support q.support) :
    2*(T.image Polymer.rightEndpoint).card≤piece.length+22 := by
  obtain ⟨vs,hh,hl,hlen,hset,hw⟩ := piece.trace.asList
  apply candidates_near_trace F (d:=1) (n:=6) (by omega) (by omega)
    (vs.map (imageIndex F 1))
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
    refine ⟨imageIndex F 1 v,?_,?_⟩
    · exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp (by rw [hset]; exact hvp),rfl⟩
    · exact q.six_rightEndpoint_contact hk hn hvq (piece.in_region v hvp).1

theorem six_root_family_count {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    (T : Finset (Polymer F))
    (hT : ∀q∈T,q.kind=.path ∧ q.length=6 ∧ Polymer.Incompatible p q) :
    T.card≤2*p.length := by
  obtain ⟨parts,hbudget,hcover⟩ := p.ring_cover (d:=1) (K:=22) (by omega) (by omega)
  let f : TracePiece (Ring F 1) → Finset (Fin 6 × ℤ) := fun piece =>
    (T.filter (fun q => ¬Disjoint piece.support q.support)).image Polymer.rightEndpoint
  have hcov : ∀ a∈T.image Polymer.rightEndpoint,∃piece∈parts,a∈f piece := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hk,hn,hi⟩ := hT q hq
    obtain ⟨piece,hpiece,hmeet⟩ := hcover q hi
      (q.path_support_avoids_deeper_core hk (by omega) (by omega))
    exact ⟨piece,hpiece,Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hmeet⟩,rfl⟩⟩
  have hc := card_le_list_sum_of_cover _ parts f hcov
  have hpart : ∀piece,2*(f piece).card≤piece.length+22 := by
    intro piece
    apply six_piece_endpoint_count
    intro q hq
    obtain ⟨hqT,hmeet⟩ := Finset.mem_filter.mp hq
    exact ⟨(hT q hqT).1,(hT q hqT).2.1,hmeet⟩
  have hsum : 2*(parts.map (fun piece => (f piece).card)).sum≤
      (parts.map TracePiece.length).sum+22*parts.length := by
    clear hc hcov hcover hbudget
    induction parts with
    | nil => simp
    | cons piece rest ih =>
      have hp := hpart piece
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add hp ih
  have hends := (Nat.mul_le_mul_left 2 hc).trans (hsum.trans hbudget)
  have ht := family_card_le_endpoint_card_mul (show 6≤20 by omega) (show 6%2=0 by omega)
    T (fun q hq => ⟨(hT q hq).1,(hT q hq).2.1⟩)
  rw [BoundaryCounts.sideCount_six] at ht
  omega

theorem long_six_length_bound {F : Rectangle} (p : Polymer F) (hp : 7≤p.length) :
    (pathLengthCount p 3 : ℝ)≤(p.length : ℝ)*(longCountCoefficient 6 : ℝ) := by
  have hh := six_root_family_count p hp
    ((shortPathSet p).filter (fun q => q.length=3+3)) (counted_path_spec p 3)
  norm_num [longCountCoefficient]
  have hh' : pathLengthCount p 3 ≤ p.length*2 := by simpa [pathLengthCount, Nat.mul_comm] using hh
  exact_mod_cast hh'

end
end RootedKP.AKLT
