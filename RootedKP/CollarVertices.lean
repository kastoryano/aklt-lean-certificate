import RootedKP.PathConfinement
import RootedKP.BoundaryCycle

namespace RootedKP.Honeycomb
set_option maxHeartbeats 800000

/-- The vertex ring has no isolated vertices: every outer core outside the
deeper core has a neighboring vertex in the same ring. -/
theorem collar_vertex_neighbor {F : Rectangle} {d : ℕ} (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4)
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
theorem collar_vertex_cell_cover {F : Rectangle} {d : ℕ} (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4)
    {v : Vertex} (hc : Core F 200 v) (hnc : ¬ Core F (200-(d+1)) v) :
    ∃ i : Fin 6, GlobalCell F 200 d i v := by
  obtain ⟨w, hadj, hwc, hwnc⟩ := collar_vertex_neighbor hd₀ hd₁ hc hnc
  have he : CollarEdge F 200 d v w := ⟨⟨hadj, Or.inl hc⟩,
    (fun h => h.2.elim hnc hwnc), hc, hwc⟩
  obtain ⟨i, hi, _⟩ := collar_edge_cell_cover hd₀ hd₁ he
  exact ⟨i, hi⟩

theorem inner_vertex_core_ring {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {v : Vertex} (hv : InnerBoundary F d v) :
    Core F 200 v ∧ ¬ Core F (200-(d+1)) v := by
  have hq := F.q_order
  have hr := F.r_order
  obtain ⟨i, τ, hl, hu, rfl⟩ := hv
  obtain ⟨r, ht⟩ : ∃ r : ℤ, τ = 2*r ∨ τ = 2*r+1 := ⟨τ/2, by omega⟩
  fin_cases i <;> rcases ht with rfl | rfl <;>
    simp only [sideChart, fromChart, vertexAt_even, vertexAt_odd, rotate,
      core_a_coordinates, core_b_coordinates] at hl hu ⊢ <;> omega

theorem inner_edge_in_collar {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {u v : Vertex} (hu : InnerBoundary F d u) (hv : InnerBoundary F d v) (he : Adj u v) :
    CollarEdge F 200 d u v := by
  have hh := inner_vertex_core_ring hd hu
  have hh' := inner_vertex_core_ring hd hv
  exact ⟨⟨he, Or.inl hh.1⟩, (fun h => h.2.elim hh.2 hh'.2), hh.1, hh'.1⟩

/-- Every leaf of the deeper sun lies on the exact inner boundary cycle. -/
theorem deeper_leaf_on_inner {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {v : Vertex} (hv : Leaf F (200-(d+1)) v) : InnerBoundary F d v := by
  have hs := leaf_on_support_height hv
  obtain ⟨w, hw, _⟩ := hv
  have hb := sun_six_height_bounds (⟨w,hw⟩ : SunVertex F (200-(d+1)) v)
  cases v with
  | a q r =>
    simp only [heightQ, heightR, heightS] at hb hs
    rcases hs with h | h | h | h | h | h
    · omega
    · refine ⟨0, 2*r, ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even] <;> omega
    · omega
    · refine ⟨2, 2*(-q-r-1), ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even, rotate] <;> omega
    · refine ⟨4, 2*q, ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even, rotate] <;> omega
    · omega
  | b q r =>
    simp only [heightQ, heightR, heightS] at hb hs
    rcases hs with h | h | h | h | h | h
    · refine ⟨3, 2*(-r-1), ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even, rotate] <;> omega
    · omega
    · refine ⟨5, 2*(q+r+1), ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even, rotate] <;> omega
    · omega
    · omega
    · refine ⟨1, 2*(-q-1), ?_, ?_, ?_⟩ <;>
        norm_num [sideChart, fromChart, vertexAt_even, rotate] <;> omega

/-- Every actual transition from the ring to a deeper core meets the inner
cycle, so maximal interior runs have the correct boundary endpoints. -/
theorem ring_to_deep_on_inner {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {u v : Vertex} (hu : ¬ Core F (200-(d+1)) u) (hv : Core F (200-(d+1)) v)
    (he : Adj u v) : InnerBoundary F d u :=
  deeper_leaf_on_inner hd (noncore_sun_vertex_is_leaf ⟨v, he, Or.inr hv⟩ hu)

end RootedKP.Honeycomb
