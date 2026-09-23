import RootedKP.InnerCoordinates
import RootedKP.CollarVertices
import RootedKP.BoundaryTraceCount

namespace RootedKP.Honeycomb
open BoundaryCycle CircleArcs
noncomputable section
set_option maxHeartbeats 0

def imageIndex (F : Rectangle) (d : ℕ) (v : Vertex) : ℤ :=
  innerIndex F d (collarMap F d v)

theorem ring_image_inner {F : Rectangle} {d : ℕ} (hd0 : 1 ≤ d) (hd1 : d ≤ 4)
    {v : Vertex} (hv : Core F 200 v ∧ ¬ Core F (200-(d+1)) v) :
    InnerBoundary F d (collarMap F d v) :=
  collarMap_image_inner hd1 (collar_vertex_cell_cover hd0 hd1 hv.1 hv.2)

theorem ring_image_step {F : Rectangle} {d : ℕ} (hd0 : 1 ≤ d) (hd1 : d ≤ 4)
    {u v : Vertex} (hu : Core F 200 u ∧ ¬ Core F (200-(d+1)) u)
    (hv : Core F 200 v ∧ ¬ Core F (200-(d+1)) v) (ha : Adj u v) :
    Near (perimeter F d) 1 (imageIndex F d u) (imageIndex F d v) := by
  apply innerIndex_near_weak hd1 (ring_image_inner hd0 hd1 hu) (ring_image_inner hd0 hd1 hv)
  apply collarMap_contracts_actual_edge hd0 hd1
  exact ⟨⟨ha,Or.inl hu.1⟩,(fun h => h.2.elim hu.2 hv.2),hu.1,hv.1⟩

/-- The actual six-cell retraction maps a ring walk to a weak circle trace. -/
theorem ring_image_trace {F : Rectangle} {d : ℕ} (hd0 : 1 ≤ d) (hd1 : d ≤ 4)
    {vs : List Vertex} (hw : ListWalk Adj vs)
    (hring : ∀ v ∈ vs, Core F 200 v ∧ ¬ Core F (200-(d+1)) v) :
    Trace (perimeter F d) (vs.map (imageIndex F d)) := by
  induction vs with
  | nil => trivial
  | cons u vs ih =>
    cases vs with
    | nil => trivial
    | cons v vs =>
      exact ⟨ring_image_step hd0 hd1 (hring u (by simp)) (hring v (by simp)) hw.1,
        ih hw.2 (fun w hw => hring w (List.mem_cons_of_mem u hw))⟩

theorem short_path_image_near {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {i j : ℕ} (hi0 : 0 < i) (hi1 : i < p.length) (hj0 : 0 < j) (hj1 : j < p.length) :
    Near (perimeter F (p.length/4-1)) (p.length-2 : ℕ)
      (imageIndex F (p.length/4-1) (p.vertex i))
      (imageIndex F (p.length/4-1) (p.vertex j)) := by
  let f : ℕ → ℤ := fun k => imageIndex F (p.length/4-1) (p.vertex (k+1))
  have hs : ∀ k < p.length-2, Near (perimeter F (p.length/4-1)) 1 (f k) (f (k+1)) := by
    intro k hk
    exact innerIndex_near_weak (by omega)
      (p.short_even_retraction_in_inner hmin hmax heven (by omega) (by omega))
      (p.short_even_retraction_in_inner hmin hmax heven (by omega) (by omega))
      (p.short_even_retraction_contracts hmin hmax heven (by omega) (by omega))
  by_cases hij : i ≤ j
  · have hh := indexed_near hs (i-1) (j-i) (by omega)
    have h₁ : i-1+1 = i := by omega
    have h₂ : i-1+(j-i)+1 = j := by omega
    simp only [f,h₁,h₂] at hh
    exact hh.mono (by omega)
  · have hh := indexed_near hs (j-1) (i-j) (by omega)
    have h₁ : j-1+1 = j := by omega
    have h₂ : j-1+(i-j)+1 = i := by omega
    simp only [f,h₁,h₂] at hh
    exact hh.symm.mono (by omega)

theorem attachment_image_coordinate {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {i : Fin 6} {r : ℤ} (hvalid : BoundaryLeaves.Valid F i r) :
    Int.ModEq (perimeter F d) (imageIndex F d (BoundaryLeaves.attachment F i r))
      (BoundaryLeaves.imageCoordinate F d (i,r)) := by
  have hp := BoundaryLeaves.parameter_valid hvalid
  unfold imageIndex BoundaryLeaves.imageCoordinate
  rw [BoundaryLeaves.attachment_eq_point,retraction_outer_point F hd i hp.1 hp.2.le]
  apply innerIndex_closed_point F hd
  · exact (clamp_mem (sideChart_inner_nonempty F d hd i)).1
  · exact (clamp_mem (sideChart_inner_nonempty F d hd i)).2

theorem path_finish_attachment {F : Rectangle} (p : BoundaryPath F 200)
    {i : Fin 6} {r : ℤ} (hvalid : BoundaryLeaves.Valid F i r)
    (hfinish : p.finish = BoundaryLeaves.leaf F i r) :
    p.vertex (p.length-1) = BoundaryLeaves.attachment F i r := by
  have hlen : 1 ≤ p.length := le_trans (by decide) (RootedKP.AKLT.boundaryPath_length_ge_three p)
  have hprev : SunAdj F 200 (BoundaryLeaves.leaf F i r) (p.vertex (p.length-1)) := by
    simpa [Nat.sub_add_cancel hlen,p.at_finish,hfinish] using
      sunAdj_symm (p.at_adjacent (p.length-1) (by omega))
  have hatt : SunAdj F 200 (BoundaryLeaves.leaf F i r) (BoundaryLeaves.attachment F i r) :=
    ⟨BoundaryLeaves.leaf_prong F i r,Or.inr (BoundaryLeaves.attachment_core hvalid)⟩
  obtain ⟨w,hw,hu⟩ := BoundaryLeaves.leaf_is_leaf hvalid
  exact (hu _ hprev).trans (hu _ hatt).symm

/-- Every internal vertex of a short even path is within n−2 projected
steps of that path's actual endpoint attachment. -/
theorem short_path_endpoint_contact {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {j : ℕ} (hj0 : 0 < j) (hj1 : j < p.length)
    {i : Fin 6} {r : ℤ} (hvalid : BoundaryLeaves.Valid F i r)
    (hfinish : p.finish = BoundaryLeaves.leaf F i r) :
    Near (perimeter F (p.length/4-1)) (p.length-2 : ℕ)
      (imageIndex F (p.length/4-1) (p.vertex j))
      (BoundaryLeaves.imageCoordinate F (p.length/4-1) (i,r)) := by
  have hh := short_path_image_near p hmin hmax heven hj0 hj1
    (show 0 < p.length-1 by omega) (show p.length-1 < p.length by omega)
  rw [path_finish_attachment p hvalid hfinish] at hh
  exact hh.mod_right (attachment_image_coordinate (by omega) hvalid)

theorem path_start_attachment {F : Rectangle} (p : BoundaryPath F 200)
    {i : Fin 6} {r : ℤ} (hvalid : BoundaryLeaves.Valid F i r)
    (hstart : p.start = BoundaryLeaves.leaf F i r) :
    p.vertex 1 = BoundaryLeaves.attachment F i r := by
  have hlen := RootedKP.AKLT.boundaryPath_length_ge_three p
  have hnext : SunAdj F 200 (BoundaryLeaves.leaf F i r) (p.vertex 1) := by
    simpa [p.at_start,hstart] using p.at_adjacent 0 (by omega)
  have hatt : SunAdj F 200 (BoundaryLeaves.leaf F i r) (BoundaryLeaves.attachment F i r) :=
    ⟨BoundaryLeaves.leaf_prong F i r,Or.inr (BoundaryLeaves.attachment_core hvalid)⟩
  obtain ⟨w,hw,hu⟩ := BoundaryLeaves.leaf_is_leaf hvalid
  exact (hu _ hnext).trans (hu _ hatt).symm

theorem short_path_start_contact {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {j : ℕ} (hj0 : 0 < j) (hj1 : j < p.length)
    {i : Fin 6} {r : ℤ} (hvalid : BoundaryLeaves.Valid F i r)
    (hstart : p.start = BoundaryLeaves.leaf F i r) :
    Near (perimeter F (p.length/4-1)) (p.length-2 : ℕ)
      (imageIndex F (p.length/4-1) (p.vertex j))
      (BoundaryLeaves.imageCoordinate F (p.length/4-1) (i,r)) := by
  have hh := short_path_image_near p hmin hmax heven hj0 hj1 (by omega : 0 < 1) (by omega : 1 < p.length)
  rw [path_start_attachment p hvalid hstart] at hh
  exact hh.mod_right (attachment_image_coordinate (by omega) hvalid)

end
end RootedKP.Honeycomb
