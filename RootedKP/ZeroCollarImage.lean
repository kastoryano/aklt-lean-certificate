import RootedKP.ZeroCollar
import RootedKP.SixPathCounts
namespace RootedKP.Honeycomb.ZeroCollar
open BoundaryCycle CircleArcs
noncomputable section
set_option maxHeartbeats 0
theorem collar_vertex_neighbor {F : Rectangle} {d : ℕ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4)
    {v : Vertex} (hc : Core F 200 v) (hnc : ¬ Core F (200-(d+1)) v) :
    ∃ w, Adj v w ∧ Core F 200 w ∧ ¬ Core F (200-(d+1)) w := by
  classical
  have hq := F.q_order
  have hr := F.r_order
  cases v with
  | a q r =>
    by_cases h₀ : Core F 200 (.b q r) ∧ ¬ Core F (200-(d+1)) (.b q r)
    · exact ⟨.b q r, by simp [Adj], h₀⟩
    by_cases h₁ : Core F 200 (.b (q-1) r) ∧ ¬ Core F (200-(d+1)) (.b (q-1) r)
    · exact ⟨.b (q-1) r, by simp [Adj], h₁⟩
    refine ⟨.b q (r-1), by simp [Adj], ?_⟩
    simp only [core_a_coordinates, core_b_coordinates] at hc hnc h₀ h₁ ⊢
    omega
  | b q r =>
    by_cases h₀ : Core F 200 (.a q r) ∧ ¬ Core F (200-(d+1)) (.a q r)
    · exact ⟨.a q r, by simp [Adj], h₀⟩
    by_cases h₁ : Core F 200 (.a (q+1) r) ∧ ¬ Core F (200-(d+1)) (.a (q+1) r)
    · exact ⟨.a (q+1) r, by simp [Adj], h₁⟩
    refine ⟨.a q (r+1), by simp [Adj], ?_⟩
    simp only [core_a_coordinates, core_b_coordinates] at hc hnc h₀ h₁ ⊢
    omega

/-- Every literal ring vertex belongs to the proved six-cell retraction
domain, without assuming that a particular incident root edge stays there. -/
theorem collar_vertex_cell_cover {F : Rectangle} {d : ℕ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4)
    {v : Vertex} (hc : Core F 200 v) (hnc : ¬ Core F (200-(d+1)) v) :
    ∃ i : Fin 6, GlobalCell F 200 d i v := by
  obtain ⟨w, hadj, hwc, hwnc⟩ := collar_vertex_neighbor hd₀ hd₁ hc hnc
  have he : CollarEdge F 200 d v w := ⟨⟨hadj, Or.inl hc⟩,
    (fun h => h.2.elim hnc hwnc), hc, hwc⟩
  obtain ⟨i, hi, _⟩ := collar_edge_cell_cover hd₀ hd₁ he
  exact ⟨i, hi⟩

theorem collarMap_contracts_actual_edge {F : Rectangle} {d : ℕ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4) {u v : Vertex} (h : CollarEdge F 200 d u v) :
    collarMap F d u = collarMap F d v ∨ Adj (collarMap F d u) (collarMap F d v) := by
  obtain ⟨i, hiu, hiv⟩ := collar_edge_cell_cover hd₀ hd₁ h
  rw [collarMap_on_cell hd₁ hiu, collarMap_on_cell hd₁ hiv]
  exact chartImage_contracts F d i h.1.1

theorem ring_image_inner {F : Rectangle} {d : ℕ} (hd0 : 0 ≤ d) (hd1 : d ≤ 4)
    {v : Vertex} (hv : Core F 200 v ∧ ¬ Core F (200-(d+1)) v) :
    InnerBoundary F d (collarMap F d v) :=
  collarMap_image_inner hd1 (collar_vertex_cell_cover hd0 hd1 hv.1 hv.2)

theorem ring_image_step {F : Rectangle} {d : ℕ} (hd0 : 0 ≤ d) (hd1 : d ≤ 4)
    {u v : Vertex} (hu : Core F 200 u ∧ ¬ Core F (200-(d+1)) u)
    (hv : Core F 200 v ∧ ¬ Core F (200-(d+1)) v) (ha : Adj u v) :
    Near (perimeter F d) 1 (imageIndex F d u) (imageIndex F d v) := by
  apply innerIndex_near_weak hd1 (ring_image_inner hd0 hd1 hu) (ring_image_inner hd0 hd1 hv)
  apply collarMap_contracts_actual_edge hd0 hd1
  exact ⟨⟨ha,Or.inl hu.1⟩,(fun h => h.2.elim hu.2 hv.2),hu.1,hv.1⟩

/-- The actual six-cell retraction maps a ring walk to a weak circle trace. -/
theorem ring_image_trace {F : Rectangle} {d : ℕ} (hd0 : 0 ≤ d) (hd1 : d ≤ 4)
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

theorem fixed_collar_image_near {F : Rectangle} (p : BoundaryPath F 200)
    {d : ℕ} (hd0 : 0≤d) (hd1 : d≤4)
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
end RootedKP.Honeycomb.ZeroCollar
