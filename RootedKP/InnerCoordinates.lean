import RootedKP.BoundaryCoordinates
import RootedKP.BoundaryCycleAdjacency
import RootedKP.CircleArcs

namespace RootedKP.Honeycomb.BoundaryCycle
open CircleArcs
noncomputable section
open Classical
set_option maxHeartbeats 0

def innerParameter (F : Rectangle) (d : ℕ) (v : Vertex) : Fin 6 × ℤ :=
  if h : ∃ a : Fin 6 × ℤ, lower F d a.1 ≤ a.2 ∧ a.2 < upper F a.1 ∧
      v = point F d a.1 a.2 then Classical.choose h else (0,0)

theorem innerParameter_spec {F : Rectangle} {d : ℕ} (hd : d ≤ 4) {v : Vertex}
    (hv : InnerBoundary F d v) :
    lower F d (innerParameter F d v).1 ≤ (innerParameter F d v).2 ∧
    (innerParameter F d v).2 < upper F (innerParameter F d v).1 ∧
    v = point F d (innerParameter F d v).1 (innerParameter F d v).2 := by
  have h : ∃ a : Fin 6 × ℤ, lower F d a.1 ≤ a.2 ∧ a.2 < upper F a.1 ∧
      v = point F d a.1 a.2 := by
    obtain ⟨i,τ,h0,h1,he⟩ := (inner_iff_halfopen F hd v).mp hv
    exact ⟨(i,τ),h0,h1,he⟩
  simp only [innerParameter,dif_pos h]
  exact Classical.choose_spec h

def innerIndex (F : Rectangle) (d : ℕ) (v : Vertex) : ℤ :=
  coordinate F d (innerParameter F d v).1 (innerParameter F d v).2

theorem innerIndex_range {F : Rectangle} {d : ℕ} (hd : d ≤ 4) {v : Vertex}
    (hv : InnerBoundary F d v) : 0 ≤ innerIndex F d v ∧ innerIndex F d v < perimeter F d := by
  have h := innerParameter_spec hd hv
  exact coordinate_range F hd _ h.1 h.2.1

theorem innerIndex_point (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (i : Fin 6) (τ : ℤ)
    (h0 : lower F d i ≤ τ) (h1 : τ < upper F i) :
    innerIndex F d (point F d i τ) = coordinate F d i τ := by
  have hv : InnerBoundary F d (point F d i τ) := ⟨i,τ,h0,h1.le,rfl⟩
  have hs := innerParameter_spec hd hv
  have he := halfopen_injective F hd h0 h1 hs.1 hs.2.1 hs.2.2
  unfold innerIndex
  rw [← he.1,← he.2]

theorem coordinate_joint_mod (F : Rectangle) (d : ℕ) (i : Fin 6) :
    Int.ModEq (perimeter F d) (coordinate F d (nextSide i) (lower F d (nextSide i)))
      (coordinate F d i (upper F i)) := by
  have he : coordinate F d (nextSide i) (lower F d (nextSide i)) =
      if i.val = 5 then coordinate F d i (upper F i) - perimeter F d
      else coordinate F d i (upper F i) := by
    fin_cases i <;>
      simp only [coordinate,offset,perimeter,baseLength,width,height,lower,upper,
        sideChart,nextSide] <;> norm_num <;> omega
  rw [he]
  split_ifs <;> simp [Int.ModEq]

theorem innerIndex_closed_point (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (i : Fin 6) (τ : ℤ)
    (h0 : lower F d i ≤ τ) (h1 : τ ≤ upper F i) :
    Int.ModEq (perimeter F d) (innerIndex F d (point F d i τ)) (coordinate F d i τ) := by
  by_cases hlt : τ < upper F i
  · rw [innerIndex_point F hd i τ h0 hlt]
  · have heq : τ = upper F i := by omega
    subst τ
    rw [joint,innerIndex_point F hd _ _ (le_refl _) (range_nonempty F hd _)]
    exact coordinate_joint_mod F d i

theorem coordinate_joint_near (F : Rectangle) (d : ℕ) (i : Fin 6) {τ : ℤ}
    (ht : τ+1 = upper F i) :
    Near (perimeter F d) 1 (coordinate F d i τ)
      (coordinate F d (nextSide i) (lower F d (nextSide i))) := by
  refine ⟨1,by omega,le_rfl,?_⟩
  have heq : coordinate F d i τ+1 = coordinate F d i (upper F i) := by
    dsimp only [coordinate]
    omega
  rw [heq]
  exact (coordinate_joint_mod F d i).symm

theorem innerIndex_near {F : Rectangle} {d : ℕ} (hd : d ≤ 4) {u v : Vertex}
    (hu : InnerBoundary F d u) (hv : InnerBoundary F d v) (ha : Adj u v) :
    Near (perimeter F d) 1 (innerIndex F d u) (innerIndex F d v) := by
  obtain ⟨i,τ,hτ0,hτ1,rfl⟩ := (inner_iff_halfopen F hd u).mp hu
  obtain ⟨j,σ,hσ0,hσ1,rfl⟩ := (inner_iff_halfopen F hd v).mp hv
  rw [innerIndex_point F hd i τ hτ0 hτ1,innerIndex_point F hd j σ hσ0 hσ1]
  rcases adjacent_parameters F hd i j τ σ hτ0 hτ1 hσ0 hσ1 ha with
    ⟨rfl,hnext | hprev⟩ | ⟨rfl,hend,rfl⟩ | ⟨rfl,hend,rfl⟩
  · refine ⟨1,by omega,le_rfl,?_⟩
    have : coordinate F d i τ + 1 = coordinate F d i σ := by dsimp [coordinate]; omega
    rw [this]
  · refine ⟨-1,le_rfl,by omega,?_⟩
    have : coordinate F d i τ + -1 = coordinate F d i σ := by dsimp [coordinate]; omega
    rw [this]
  · exact coordinate_joint_near F d i hend
  · exact (coordinate_joint_near F d j hend).symm

theorem innerIndex_near_weak {F : Rectangle} {d : ℕ} (hd : d ≤ 4) {u v : Vertex}
    (hu : InnerBoundary F d u) (hv : InnerBoundary F d v) (ha : u = v ∨ Adj u v) :
    Near (perimeter F d) 1 (innerIndex F d u) (innerIndex F d v) := by
  rcases ha with rfl | ha
  · exact (Near.refl _ _).mono (by omega)
  · exact innerIndex_near hd hu hv ha

end
end RootedKP.Honeycomb.BoundaryCycle
