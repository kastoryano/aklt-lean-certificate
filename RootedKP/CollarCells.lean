import RootedKP.Geometry
import Mathlib.Tactic.Convert
import RootedKP.SideSeparation

/-! Exact six-cell coordinates for the fixed-radius collar. -/
namespace RootedKP.Honeycomb

set_option maxHeartbeats 800000

def inverseRotate : Vertex → Vertex
  | .a q r => .b (q + r) (-q - 1)
  | .b q r => .a (q + r + 1) (-q - 1)

theorem rotate_inverseRotate (v : Vertex) : rotate (inverseRotate v) = v := by
  cases v <;> simp only [inverseRotate, rotate] <;> congr 1 <;> omega

theorem inverseRotate_rotate (v : Vertex) : inverseRotate (rotate v) = v := by
  cases v <;> simp only [inverseRotate, rotate] <;> congr 1 <;> omega

/-- Literal vertex inequalities of a side's face-row cell, including the
initial whisker. The two sublattices differ at the terminal corner. -/
def InCell (Q r₀ r₁ : ℤ) (d : ℕ) : Vertex → Prop
  | .a q r => Q - d ≤ q ∧ q ≤ Q ∧ r ≤ r₁ ∧ Q + r₀ ≤ q + r
  | .b q r => Q - d ≤ q ∧ q ≤ Q ∧ r ≤ r₁ ∧ Q + r₀ - 1 ≤ q + r ∧
      (q < Q ∨ r < r₁)

/-- Overlapping neighboring cells share precisely the right-connector
coordinate layer; this implication includes its intermediate vertices. -/
theorem adjacent_cell_overlap {Q r₀ r₁ r₂ : ℤ} {d : ℕ} {v : Vertex}
    (h₀ : InCell Q r₀ r₁ d v)
    (h₁ : InCell (Q + r₁) (-Q) r₂ d (inverseRotate v)) :
    match v with
    | .a q r => r = r₁ ∧ Q - d ≤ q ∧ q ≤ Q
    | .b q r => r = r₁ ∧ Q - d ≤ q ∧ q < Q := by
  cases v <;> simp only [InCell, inverseRotate] at h₀ h₁ ⊢ <;> omega

theorem vertexAt_lower_endpoint (Q r : ℤ) :
    vertexAt Q (2 * r - 1) = .b Q (r - 1) := by
  convert vertexAt_odd Q (r - 1) using 1 <;> congr 1 <;> omega

/-- The local maps agree on every vertex of neighboring cells, including
both sublattices along the complete shared connector. -/
theorem adjacent_cell_gluing {Q r₀ r₁ r₂ : ℤ} {d : ℕ} {v : Vertex}
    (hlen : 2 * (r₀ + d) - 1 ≤ 2 * r₁)
    (h₀ : InCell Q r₀ r₁ d v)
    (h₁ : InCell (Q + r₁) (-Q) r₂ d (inverseRotate v)) :
    localMap Q r₀ r₁ d v =
      rotate (localMap (Q + r₁) (-Q) r₂ d (inverseRotate v)) := by
  have hov := adjacent_cell_overlap h₀ h₁
  cases v with
  | a q r =>
      obtain ⟨rfl, hlo, hhi⟩ := hov
      simp only [localMap, inverseRotate, heightR]
      rw [clamp_of_above hlen (by omega), clamp_of_below (by omega),
        vertexAt_even, vertexAt_lower_endpoint]
      simp only [rotate]
      congr 1 <;> omega
  | b q r =>
      obtain ⟨rfl, hlo, hhi⟩ := hov
      simp only [localMap, inverseRotate, heightR]
      rw [clamp_of_above hlen (by omega), clamp_of_below (by omega),
        vertexAt_even, vertexAt_lower_endpoint]
      simp only [rotate]
      congr 1 <;> omega

structure SideChart where
  Q : ℤ
  r₀ : ℤ
  r₁ : ℤ

def sideChart (F : Rectangle) (R : ℕ) (i : Fin 6) : SideChart :=
  match i.val with
  | 0 => ⟨F.qmax + R, F.rmin - R, F.rmax⟩
  | 1 => ⟨F.qmax + F.rmax + R, -F.qmax - R, -F.qmax⟩
  | 2 => ⟨F.rmax + R, -F.qmax - F.rmax - R, -F.qmin - F.rmax⟩
  | 3 => ⟨-F.qmin + R, -F.rmax - R, -F.rmin⟩
  | 4 => ⟨-F.qmin - F.rmin + R, F.qmin - R, F.qmin⟩
  | _ => ⟨-F.rmin + R, F.qmin + F.rmin - R, F.qmax + F.rmin⟩

def toChart (i : Fin 6) (v : Vertex) : Vertex :=
  match i.val with
  | 0 => v
  | 1 => inverseRotate v
  | 2 => inverseRotate (inverseRotate v)
  | 3 => inverseRotate (inverseRotate (inverseRotate v))
  | 4 => inverseRotate (inverseRotate (inverseRotate (inverseRotate v)))
  | _ => inverseRotate (inverseRotate (inverseRotate (inverseRotate (inverseRotate v))))

def GlobalCell (F : Rectangle) (R d : ℕ) (i : Fin 6) (v : Vertex) : Prop :=
  let c := sideChart F R i
  InCell c.Q c.r₀ c.r₁ d (toChart i v)

def fromChart (i : Fin 6) (v : Vertex) : Vertex :=
  match i.val with
  | 0 => v
  | 1 => rotate v
  | 2 => rotate (rotate v)
  | 3 => rotate (rotate (rotate v))
  | 4 => rotate (rotate (rotate (rotate v)))
  | _ => rotate (rotate (rotate (rotate (rotate v))))

def nextSide (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

theorem inverseRotate_six (v : Vertex) :
    inverseRotate (inverseRotate (inverseRotate (inverseRotate (inverseRotate (inverseRotate v))))) = v := by
  cases v <;> simp only [inverseRotate] <;> congr 1 <;> omega

theorem toChart_next (i : Fin 6) (v : Vertex) :
    toChart (nextSide i) v = inverseRotate (toChart i v) := by
  fin_cases i <;> simp only [toChart, nextSide]
  exact (inverseRotate_six v).symm

theorem fromChart_next (i : Fin 6) (v : Vertex) :
    fromChart (nextSide i) v = fromChart i (rotate v) := by
  fin_cases i <;> simp only [fromChart, nextSide]
  exact (rotate_six v).symm

theorem sideChart_next_Q (F : Rectangle) (R : ℕ) (i : Fin 6) :
    (sideChart F R (nextSide i)).Q = (sideChart F R i).Q + (sideChart F R i).r₁ := by
  fin_cases i <;> simp only [sideChart, nextSide] <;> omega

theorem sideChart_next_r₀ (F : Rectangle) (R : ℕ) (i : Fin 6) :
    (sideChart F R (nextSide i)).r₀ = -(sideChart F R i).Q := by
  fin_cases i <;> simp only [sideChart, nextSide] <;> omega

theorem sideChart_inner_nonempty (F : Rectangle) (d : ℕ) (hd : d ≤ 4) (i : Fin 6) :
    2 * ((sideChart F 200 i).r₀ + d) - 1 ≤ 2 * (sideChart F 200 i).r₁ := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> simp only [sideChart] <;> omega

def chartImage (F : Rectangle) (d : ℕ) (i : Fin 6) (v : Vertex) : Vertex :=
  let c := sideChart F 200 i
  fromChart i (localMap c.Q c.r₀ c.r₁ d (toChart i v))

theorem next_cell_gluing {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    (i : Fin 6) {v : Vertex}
    (hi : GlobalCell F 200 d i v) (hj : GlobalCell F 200 d (nextSide i) v) :
    chartImage F d i v = chartImage F d (nextSide i) v := by
  dsimp only [GlobalCell] at hi hj
  rw [toChart_next, sideChart_next_Q, sideChart_next_r₀] at hj
  have heq := adjacent_cell_gluing (sideChart_inner_nonempty F d hd i) hi hj
  dsimp only [chartImage]
  rw [toChart_next, sideChart_next_Q, sideChart_next_r₀, fromChart_next]
  exact congrArg (fromChart i) heq

/-- Nonadjacent coordinate cells cannot meet in this collar. -/
theorem globalCell_overlap_same_or_adjacent {F : Rectangle} {d : ℕ}
    (hd : d ≤ 4) {i j : Fin 6} {v : Vertex}
    (hi : GlobalCell F 200 d i v) (hj : GlobalCell F 200 d j v) :
    i = j ∨ SideAdjacent i j := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;> cases v <;>
    simp [GlobalCell, sideChart, toChart, inverseRotate, InCell, SideAdjacent] at hi hj ⊢ <;>
    omega

/-- Pairwise agreement of the six local maps on every actual overlap. -/
theorem global_cell_gluing {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {i j : Fin 6} {v : Vertex}
    (hi : GlobalCell F 200 d i v) (hj : GlobalCell F 200 d j v) :
    chartImage F d i v = chartImage F d j v := by
  rcases globalCell_overlap_same_or_adjacent hd hi hj with hij | hij
  · subst j
    rfl
  · rcases hij with hij | hij
    · have heq : nextSide i = j := Fin.ext hij
      subst j
      exact next_cell_gluing hd i hi hj
    · have heq : nextSide j = i := Fin.ext hij
      subst i
      exact (next_cell_gluing hd j hj hi).symm

/-- The actual outer sun minus deeper-sun edges, after removing outer prongs. -/
def CollarEdge (F : Rectangle) (R d : ℕ) (u v : Vertex) : Prop :=
  SunAdj F R u v ∧ ¬ SunAdj F (R - (d + 1)) u v ∧ Core F R u ∧ Core F R v

private theorem collar_cover_edge0 {F : Rectangle} {d : ℕ}
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
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
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
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
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) (q r : ℤ)
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
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) {u v : Vertex}
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

theorem inverseRotate_adj {u v : Vertex} (h : Adj u v) :
    Adj (inverseRotate u) (inverseRotate v) := by
  cases u <;> cases v <;> simp_all [inverseRotate, Adj] <;> omega

theorem toChart_adj (i : Fin 6) {u v : Vertex} (h : Adj u v) :
    Adj (toChart i u) (toChart i v) := by
  fin_cases i <;> simp only [toChart]
  · exact h
  · exact inverseRotate_adj h
  · exact inverseRotate_adj (inverseRotate_adj h)
  · exact inverseRotate_adj (inverseRotate_adj (inverseRotate_adj h))
  · exact inverseRotate_adj (inverseRotate_adj (inverseRotate_adj (inverseRotate_adj h)))
  · exact inverseRotate_adj (inverseRotate_adj (inverseRotate_adj (inverseRotate_adj (inverseRotate_adj h))))

theorem fromChart_adj (i : Fin 6) {u v : Vertex} (h : Adj u v) :
    Adj (fromChart i u) (fromChart i v) := by
  fin_cases i <;> simp only [fromChart]
  · exact h
  · exact rotate_adj h
  · exact rotate_adj (rotate_adj h)
  · exact rotate_adj (rotate_adj (rotate_adj h))
  · exact rotate_adj (rotate_adj (rotate_adj (rotate_adj h)))
  · exact rotate_adj (rotate_adj (rotate_adj (rotate_adj (rotate_adj h))))

theorem toChart_fromChart (i : Fin 6) (v : Vertex) :
    toChart i (fromChart i v) = v := by
  fin_cases i <;> simp only [toChart, fromChart, inverseRotate_rotate]

theorem chartImage_contracts (F : Rectangle) (d : ℕ) (i : Fin 6) {u v : Vertex}
    (h : Adj u v) :
    chartImage F d i u = chartImage F d i v ∨ Adj (chartImage F d i u) (chartImage F d i v) := by
  have hc := localMap_contracts (sideChart F 200 i).Q (sideChart F 200 i).r₀
    (sideChart F 200 i).r₁ d (toChart_adj i h)
  rcases hc with hc | hc
  · exact Or.inl (congrArg (fromChart i) hc)
  · exact Or.inr (fromChart_adj i hc)

/-- A globally well-defined map: any available cell gives the same value.
The default outside the six-cell domain is irrelevant to collar edges. -/
noncomputable def collarMap (F : Rectangle) (d : ℕ) (v : Vertex) : Vertex := by
  classical
  exact if h : ∃ i : Fin 6, GlobalCell F 200 d i v then
    chartImage F d (Classical.choose h) v else v

theorem collarMap_on_cell {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {i : Fin 6} {v : Vertex} (hi : GlobalCell F 200 d i v) :
    collarMap F d v = chartImage F d i v := by
  classical
  unfold collarMap
  split_ifs with h
  · exact global_cell_gluing hd (Classical.choose_spec h) hi
  · exact False.elim (h ⟨i, hi⟩)

/-- The global map contracts every edge of the actual collar, at all
rectangle sizes. Coverage and gluing have been proved above. -/
theorem collarMap_contracts_actual_edge {F : Rectangle} {d : ℕ}
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) {u v : Vertex} (h : CollarEdge F 200 d u v) :
    collarMap F d u = collarMap F d v ∨ Adj (collarMap F d u) (collarMap F d v) := by
  obtain ⟨i, hiu, hiv⟩ := collar_edge_cell_cover hd₀ hd₁ h
  rw [collarMap_on_cell hd₁ hiu, collarMap_on_cell hd₁ hiv]
  exact chartImage_contracts F d i h.1.1

theorem inner_arc_in_cell (Q r₀ r₁ τ : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hl : 2 * (r₀ + d) - 1 ≤ τ) (hu : τ ≤ 2 * r₁) :
    InCell Q r₀ r₁ d (vertexAt (Q - d) τ) := by
  unfold vertexAt
  split_ifs <;> simp only [InCell] <;> omega

/-- The six exact inner-side zigzags, as a set of primal vertices. -/
def InnerBoundary (F : Rectangle) (d : ℕ) (v : Vertex) : Prop :=
  ∃ i : Fin 6, ∃ τ : ℤ,
    2 * ((sideChart F 200 i).r₀ + d) - 1 ≤ τ ∧ τ ≤ 2 * (sideChart F 200 i).r₁ ∧
    v = fromChart i (vertexAt ((sideChart F 200 i).Q - d) τ)

theorem collarMap_fixes_inner {F : Rectangle} {d : ℕ}
    (hd₀ : 1 ≤ d) (hd₁ : d ≤ 4) {v : Vertex} (hv : InnerBoundary F d v) :
    collarMap F d v = v := by
  obtain ⟨i, τ, hl, hu, rfl⟩ := hv
  have hi : GlobalCell F 200 d i
      (fromChart i (vertexAt ((sideChart F 200 i).Q - d) τ)) := by
    dsimp only [GlobalCell]
    rw [toChart_fromChart]
    exact inner_arc_in_cell _ _ _ _ _ hd₀ hl hu
  rw [collarMap_on_cell hd₁ hi]
  dsimp only [chartImage]
  rw [toChart_fromChart, localMap_fixes_inner _ _ _ _ _ hl hu]

theorem collarMap_image_inner {F : Rectangle} {d : ℕ} (hd : d ≤ 4)
    {v : Vertex} (hv : ∃ i : Fin 6, GlobalCell F 200 d i v) :
    InnerBoundary F d (collarMap F d v) := by
  obtain ⟨i, hi⟩ := hv
  rw [collarMap_on_cell hd hi]
  refine ⟨i, clamp (2 * ((sideChart F 200 i).r₀ + d) - 1)
    (2 * (sideChart F 200 i).r₁) (heightR (toChart i v)), ?_, ?_, rfl⟩
  · exact (clamp_mem (sideChart_inner_nonempty F d hd i)).1
  · exact (clamp_mem (sideChart_inner_nonempty F d hd i)).2

end RootedKP.Honeycomb
