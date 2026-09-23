import RootedKP.CollarVertices

namespace RootedKP.Honeycomb.ZeroCollar
set_option maxHeartbeats 0
private theorem collar_cover_edge0 {F : Rectangle} {d : ℕ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
    (h : CollarEdge F 200 d (.a q r) (.b q r)) :
    ∃ i : Fin 6, GlobalCell F 200 d i (.a q r) ∧ GlobalCell F 200 d i (.b q r) := by
  have hq := F.q_order
  have hr := F.r_order
  have hcu := h.2.2.1
  have hcv := h.2.2.2
  have hnu : ¬ Core F (200 - (d + 1)) (.a q r) := fun hc => h.2.1 ⟨h.1.1, Or.inl hc⟩
  have hnv : ¬ Core F (200 - (d + 1)) (.b q r) := fun hc => h.2.1 ⟨h.1.1, Or.inr hc⟩
  clear h
  simp only [core_a_coordinates, core_b_coordinates, not_and_or, not_le] at hnu hnv
  simp only [core_a_coordinates, core_b_coordinates] at hcu hcv
  rcases hnu with hnu | hnu | hnu | hnu | hnu | hnu
  · by_cases hi : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b q r)
    · exact ⟨3, hi⟩
    · by_cases hj : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b q r)
      · exact ⟨2, hj⟩
      · refine ⟨4, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b q r)
    · exact ⟨0, hi⟩
    · by_cases hj : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b q r)
      · exact ⟨5, hj⟩
      · refine ⟨1, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b q r)
    · exact ⟨5, hi⟩
    · by_cases hj : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b q r)
      · exact ⟨4, hj⟩
      · refine ⟨0, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b q r)
    · exact ⟨2, hi⟩
    · by_cases hj : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b q r)
      · exact ⟨1, hj⟩
      · refine ⟨3, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b q r)
    · exact ⟨4, hi⟩
    · by_cases hj : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b q r)
      · exact ⟨3, hj⟩
      · refine ⟨5, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b q r)
    · exact ⟨1, hi⟩
    · by_cases hj : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b q r)
      · exact ⟨0, hj⟩
      · refine ⟨2, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega

private theorem collar_cover_edge1 {F : Rectangle} {d : ℕ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
    (h : CollarEdge F 200 d (.a q r) (.b (q - 1) r)) :
    ∃ i : Fin 6, GlobalCell F 200 d i (.a q r) ∧ GlobalCell F 200 d i (.b (q - 1) r) := by
  have hq := F.q_order
  have hr := F.r_order
  have hcu := h.2.2.1
  have hcv := h.2.2.2
  have hnu : ¬ Core F (200 - (d + 1)) (.a q r) := fun hc => h.2.1 ⟨h.1.1, Or.inl hc⟩
  have hnv : ¬ Core F (200 - (d + 1)) (.b (q - 1) r) := fun hc => h.2.1 ⟨h.1.1, Or.inr hc⟩
  clear h
  simp only [core_a_coordinates, core_b_coordinates, not_and_or, not_le] at hnu hnv
  simp only [core_a_coordinates, core_b_coordinates] at hcu hcv
  rcases hnu with hnu | hnu | hnu | hnu | hnu | hnu
  · by_cases hi : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b (q - 1) r)
    · exact ⟨3, hi⟩
    · by_cases hj : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b (q - 1) r)
      · exact ⟨2, hj⟩
      · refine ⟨4, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b (q - 1) r)
    · exact ⟨0, hi⟩
    · by_cases hj : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b (q - 1) r)
      · exact ⟨5, hj⟩
      · refine ⟨1, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b (q - 1) r)
    · exact ⟨5, hi⟩
    · by_cases hj : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b (q - 1) r)
      · exact ⟨4, hj⟩
      · refine ⟨0, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b (q - 1) r)
    · exact ⟨2, hi⟩
    · by_cases hj : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b (q - 1) r)
      · exact ⟨1, hj⟩
      · refine ⟨3, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b (q - 1) r)
    · exact ⟨4, hi⟩
    · by_cases hj : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b (q - 1) r)
      · exact ⟨3, hj⟩
      · refine ⟨5, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b (q - 1) r)
    · exact ⟨1, hi⟩
    · by_cases hj : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b (q - 1) r)
      · exact ⟨0, hj⟩
      · refine ⟨2, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega

private theorem collar_cover_edge2 {F : Rectangle} {d : ℕ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
    (h : CollarEdge F 200 d (.a q r) (.b q (r - 1))) :
    ∃ i : Fin 6, GlobalCell F 200 d i (.a q r) ∧ GlobalCell F 200 d i (.b q (r - 1)) := by
  have hq := F.q_order
  have hr := F.r_order
  have hcu := h.2.2.1
  have hcv := h.2.2.2
  have hnu : ¬ Core F (200 - (d + 1)) (.a q r) := fun hc => h.2.1 ⟨h.1.1, Or.inl hc⟩
  have hnv : ¬ Core F (200 - (d + 1)) (.b q (r - 1)) := fun hc => h.2.1 ⟨h.1.1, Or.inr hc⟩
  clear h
  simp only [core_a_coordinates, core_b_coordinates, not_and_or, not_le] at hnu hnv
  simp only [core_a_coordinates, core_b_coordinates] at hcu hcv
  rcases hnu with hnu | hnu | hnu | hnu | hnu | hnu
  · by_cases hi : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b q (r - 1))
    · exact ⟨3, hi⟩
    · by_cases hj : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b q (r - 1))
      · exact ⟨2, hj⟩
      · refine ⟨4, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b q (r - 1))
    · exact ⟨0, hi⟩
    · by_cases hj : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b q (r - 1))
      · exact ⟨5, hj⟩
      · refine ⟨1, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 5 (.a q r) ∧ GlobalCell F 200 d 5 (.b q (r - 1))
    · exact ⟨5, hi⟩
    · by_cases hj : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b q (r - 1))
      · exact ⟨4, hj⟩
      · refine ⟨0, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 2 (.a q r) ∧ GlobalCell F 200 d 2 (.b q (r - 1))
    · exact ⟨2, hi⟩
    · by_cases hj : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b q (r - 1))
      · exact ⟨1, hj⟩
      · refine ⟨3, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 4 (.a q r) ∧ GlobalCell F 200 d 4 (.b q (r - 1))
    · exact ⟨4, hi⟩
    · by_cases hj : GlobalCell F 200 d 3 (.a q r) ∧ GlobalCell F 200 d 3 (.b q (r - 1))
      · exact ⟨3, hj⟩
      · refine ⟨5, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
  · by_cases hi : GlobalCell F 200 d 1 (.a q r) ∧ GlobalCell F 200 d 1 (.b q (r - 1))
    · exact ⟨1, hi⟩
    · by_cases hj : GlobalCell F 200 d 0 (.a q r) ∧ GlobalCell F 200 d 0 (.b q (r - 1))
      · exact ⟨0, hj⟩
      · refine ⟨2, ?_⟩
        simp [GlobalCell, sideChart, toChart, inverseRotate, InCell] at hi hj ⊢
        omega
/-- Every actual collar edge lies in a common explicit cell, at every rectangle size. -/
theorem collar_edge_cell_cover {F : Rectangle} {d : ℕ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 4) {u v : Vertex}
    (h : CollarEdge F 200 d u v) :
    ∃ i : Fin 6, GlobalCell F 200 d i u ∧ GlobalCell F 200 d i v := by
  have ha := h.1.1
  cases u with
  | a q r =>
      cases v with
      | a q' r' => exact False.elim ha
      | b q' r' =>
          rcases ha with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> subst q' <;> subst r'
          · exact collar_cover_edge0 hd₀ hd₁ q r h
          · exact collar_cover_edge1 hd₀ hd₁ q r h
          · exact collar_cover_edge2 hd₀ hd₁ q r h
  | b q r =>
      cases v with
      | b q' r' => exact False.elim ha
      | a q' r' =>
          have hs : CollarEdge F 200 d (.a q' r') (.b q r) :=
            ⟨sunAdj_symm h.1, (fun hh => h.2.1 (sunAdj_symm hh)), h.2.2.2, h.2.2.1⟩
          rcases ha with ⟨hq, hr⟩ | ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> subst q <;> subst r
          · obtain ⟨i, hu, hv⟩ := collar_cover_edge0 hd₀ hd₁ q' r' hs
            exact ⟨i, hv, hu⟩
          · obtain ⟨i, hu, hv⟩ := collar_cover_edge1 hd₀ hd₁ q' r' hs
            exact ⟨i, hv, hu⟩
          · obtain ⟨i, hu, hv⟩ := collar_cover_edge2 hd₀ hd₁ q' r' hs
            exact ⟨i, hv, hu⟩


end RootedKP.Honeycomb.ZeroCollar
