import RootedKP.ChartIsometry

/-! Actual all-size halo footprints reduce to two adjacent support inequalities. -/
namespace RootedKP.Honeycomb
set_option maxHeartbeats 0

lemma faceHalo_iff_sideMargins (F : Rectangle) (s : ℕ) (f : Face) :
    FaceHalo F s f ↔ ∀ i : Fin 6, 0 ≤ sideMargin F s f i := by
  constructor
  · exact fun h i => sideMargin_nonnegative h i
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [sideMargin] at h0 h1 h2 h3 h4 h5
    unfold FaceHalo
    omega

/-- A pairwise adjacent collection of sides of a hexagon fits in one adjacent pair. -/
lemma sides_in_adjacent_pair (P : Fin 6 → Prop)
    (hpair : ∀ i j, P i → P j → i = j ∨ SideAdjacent i j) :
    ∃ i : Fin 6, ∀ j, P j → j = i ∨ j = chartNextSide i := by
  classical
  by_cases hex : ∃ i, P i
  · obtain ⟨i,hi⟩ := hex
    by_cases hn : P (chartNextSide i)
    · refine ⟨i, ?_⟩
      intro j hj
      have ha := hpair i j hi hj
      have hb := hpair (chartNextSide i) j hn hj
      fin_cases i <;> fin_cases j <;>
        norm_num [SideAdjacent, chartNextSide] at *
    · refine ⟨chartPrevSide i, ?_⟩
      intro j hj
      have ha := hpair i j hi hj
      have hne : j ≠ chartNextSide i := fun h => hn (h ▸ hj)
      fin_cases i <;> fin_cases j <;>
        norm_num [SideAdjacent, chartNextSide, chartPrevSide] at *
  · refine ⟨0, ?_⟩
    intro j hj
    exact False.elim (hex ⟨j,hj⟩)

/-- One fixed adjacent pair describes the ENTIRE dual ball, not merely the
faces originally selected in a finite footprint. -/
theorem halo_dual_ball_pair (F : Rectangle) (s L : ℕ) (f₀ : Face)
    (hf₀ : FaceHalo F s f₀) (hsmall : 2*L < s) :
    ∃ i : Fin 6, ∀ f, DualWithin f₀ f L →
      (FaceHalo F s f ↔
        0 ≤ sideMargin F s f i ∧ 0 ≤ sideMargin F s f (chartNextSide i)) := by
  let near : Fin 6 → Prop := fun i => sideMargin F s f₀ i ≤ L
  have hpair : ∀ i j, near i → near j → i = j ∨ SideAdjacent i j := by
    intro i j hi hj
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      by_contra hsep
      have hsum := nonadjacent_margin_sum hf₀ i j hij hsep
      dsimp [near] at hi hj
      omega
  obtain ⟨i,hi⟩ := sides_in_adjacent_pair near hpair
  refine ⟨i, ?_⟩
  intro f hf
  constructor
  · intro hh
    exact ⟨sideMargin_nonnegative hh i, sideMargin_nonnegative hh (chartNextSide i)⟩
  · intro hh
    apply (faceHalo_iff_sideMargins F s f).mpr
    intro j
    by_cases hj : near j
    · rcases hi j hj with rfl | rfl
      · exact hh.1
      · exact hh.2
    · have hdist := sideMargin_lipschitz (F := F) (s := s) hf j
      dsimp [near] at hj
      omega

/-- Universal incidence-preserving corner-chart realization of every small
actual halo face footprint. Bulk and straight-side patches simply map far
from one or both boundaries of the same convex-corner chart. -/
theorem regional_face_chart (F : Rectangle) (s L : ℕ) (f₀ : Face)
    (hf₀ : FaceHalo F s f₀) (hsmall : 2*L < s) :
    ∃ e : LatticeIso, ∀ f, DualWithin f₀ f L →
      (FaceHalo F s f ↔ BoundaryCharts.FaceIn .corner (e.face f)) := by
  obtain ⟨i,hi⟩ := halo_dual_ball_pair F s L f₀ hf₀ hsmall
  refine ⟨cornerIso F s i, fun f hf => ?_⟩
  exact (hi f hf).trans (cornerIso_face_iff F s i f).symm

/-- The explicit diameter allowance needed by the short-root certificates. -/
theorem radius200_face_chart (F : Rectangle) (f₀ : Face)
    (hf₀ : FaceHalo F 200 f₀) :
    ∃ e : LatticeIso, ∀ f, DualWithin f₀ f 56 →
      (FaceHalo F 200 f ↔ BoundaryCharts.FaceIn .corner (e.face f)) :=
  regional_face_chart F 200 56 f₀ hf₀ (by decide)

end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.radius200_face_chart
