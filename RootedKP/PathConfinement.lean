import RootedKP.CollarCells
import RootedKP.PolymerLength
import Mathlib.Data.List.GetD

/-! Literal simple-path confinement, using a local three-edge deeper-sun
block instead of assuming a maximal-component decomposition. -/
namespace RootedKP.Honeycomb

/-- All six calibrated support inequalities for actual sun vertices. -/
theorem sun_six_height_bounds {F : Rectangle} {R : ℕ} {v : Vertex}
    (hv : SunVertex F R v) :
    2 * (F.qmin - R) - 3 ≤ heightQ v ∧ heightQ v ≤ 2 * (F.qmax + R) + 2 ∧
    2 * (F.rmin - R) - 3 ≤ heightR v ∧ heightR v ≤ 2 * (F.rmax + R) + 2 ∧
    2 * (F.qmin + F.rmin - R) - 4 ≤ heightS v ∧
      heightS v ≤ 2 * (F.qmax + F.rmax + R) + 1 := by
  obtain ⟨w, hadj, hcore⟩ := hv
  have hq := F.q_order
  have hr := F.r_order
  cases v <;> cases w <;>
    simp_all [Adj, core_a_coordinates, core_b_coordinates, heightQ, heightR, heightS] <;> omega

/-- Every actual leaf lies on one of the six calibrated outer support layers. -/
theorem leaf_on_support_height {F : Rectangle} {R : ℕ} {v : Vertex}
    (hv : Leaf F R v) :
    heightQ v = 2 * (F.qmin - R) - 3 ∨ heightQ v = 2 * (F.qmax + R) + 2 ∨
    heightR v = 2 * (F.rmin - R) - 3 ∨ heightR v = 2 * (F.rmax + R) + 2 ∨
    heightS v = 2 * (F.qmin + F.rmin - R) - 4 ∨
      heightS v = 2 * (F.qmax + F.rmax + R) + 1 := by
  have hnc := leaf_not_core hv
  obtain ⟨w, hwSun, huniq⟩ := hv
  have hadj := hwSun.1
  have hw := hwSun.2.resolve_left hnc
  clear huniq hwSun
  have hq := F.q_order
  have hr := F.r_order
  cases v <;> cases w <;>
    simp_all [Adj, core_a_coordinates, core_b_coordinates, heightQ, heightR, heightS] <;> omega

theorem Walk.leaf_deeper_sun_distance {F : Rectangle} {R δ n : ℕ} (hδ : δ ≤ R)
    {x y : Vertex} (h : Walk x y n) (hx : Leaf F R x)
    (hy : SunVertex F (R - δ) y) : 2 * δ ≤ n := by
  have hb := sun_six_height_bounds hy
  have hs := leaf_on_support_height hx
  have hq := h.height_bounds heightQ_lipschitz
  have hr := h.height_bounds heightR_lipschitz
  have hsum := h.height_bounds heightS_lipschitz
  omega

private theorem walk_snoc {u v w : Vertex} {n : ℕ} (h : Walk u v n) (he : Adj v w) :
    Walk u w (n + 1) := by
  induction h with
  | nil v => exact Walk.cons he (Walk.nil w)
  | cons huv hvw ih => exact Walk.cons huv (ih he)

theorem Walk.reverse {u v : Vertex} {n : ℕ} (h : Walk u v n) : Walk v u n := by
  induction h with
  | nil v => exact Walk.nil v
  | cons huv hvw ih => exact walk_snoc ih (adj_symm huv)

/-- Indexed consecutive edges give every exact subwalk, without a decomposition assumption. -/
theorem indexed_subwalk {v : ℕ → Vertex} {n : ℕ}
    (he : ∀ i, i < n → Adj (v i) (v (i + 1))) (i k : ℕ) (hik : i + k ≤ n) :
    Walk (v i) (v (i + k)) k := by
  induction k generalizing i with
  | zero => simpa using Walk.nil (v i)
  | succ k ih =>
      have hh := Walk.cons (he i (by omega)) (ih (i + 1) (by omega))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

namespace IndexedConfinement

variable {F : Rectangle} {R δ n : ℕ} {v : ℕ → Vertex}

theorem deep_vertex_positions (hδ : δ ≤ R)
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    {i : ℕ} (hi : i ≤ n) (hv : SunVertex F (R - δ) (v i)) :
    2 * δ ≤ i ∧ 2 * δ ≤ n - i := by
  have hwalk := fun j hj => (he j hj).1
  have hpre : Walk (v 0) (v i) i := by simpa using indexed_subwalk hwalk 0 i (by omega)
  have hsuf : Walk (v i) (v n) (n - i) := by
    simpa [Nat.add_sub_of_le hi] using indexed_subwalk hwalk i (n - i) (by omega)
  exact ⟨hpre.leaf_deeper_sun_distance hδ hstart hv,
    hsuf.reverse.leaf_deeper_sun_distance hδ hfinish hv⟩

theorem deep_core_interior
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    {i : ℕ} (hi : i ≤ n) (hc : Core F (R - δ) (v i)) : 0 < i ∧ i < n := by
  have houter := core_mono (Nat.sub_le R δ) hc
  have hs := leaf_not_core hstart
  have ht := leaf_not_core hfinish
  constructor
  · by_contra h
    have heq : i = 0 := by omega
    exact hs (heq ▸ houter)
  · by_contra h
    have heq : i = n := by omega
    exact ht (heq ▸ houter)

/-- Simplicity forces a second neighboring core whenever a path visits a
core: two distinct path neighbors cannot both be noncores. -/
theorem adjacent_deep_cores
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hinj : ∀ i, i ≤ n → ∀ j, j ≤ n → v i = v j → i = j)
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    {i : ℕ} (hi : i ≤ n) (hc : Core F (R - δ) (v i)) :
    ∃ k, k + 1 ≤ n ∧ Core F (R - δ) (v k) ∧ Core F (R - δ) (v (k + 1)) := by
  have hinter := deep_core_interior hstart hfinish hi hc
  have hpred : i - 1 + 1 = i := by omega
  classical
  by_cases hp : Core F (R - δ) (v (i - 1))
  · refine ⟨i - 1, by omega, hp, ?_⟩
    simpa [hpred] using hc
  · have hn : Core F (R - δ) (v (i + 1)) := by
      by_contra hn
      have hprev : Adj (v i) (v (i - 1)) := by
        simpa [hpred] using adj_symm (he (i - 1) (by omega)).1
      have heq := core_noncore_neighbor_unique hc hp hn hprev (he i hinter.2).1
      have hh := hinj (i - 1) (by omega) (i + 1) (by omega) heq
      omega
    exact ⟨i, by omega, hc, hn⟩

/-- Visiting a deeper core forces a literal three-edge deeper-sun block and
therefore the full `4δ+3` lower bound. No component extraction is assumed. -/
theorem deep_core_forces_length (hδ : δ ≤ R)
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hinj : ∀ i, i ≤ n → ∀ j, j ≤ n → v i = v j → i = j)
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    {i : ℕ} (hi : i ≤ n) (hc : Core F (R - δ) (v i)) : 4 * δ + 3 ≤ n := by
  obtain ⟨k, hk, hkcore, hnextcore⟩ := adjacent_deep_cores he hinj hstart hfinish hi hc
  have hkint := deep_core_interior hstart hfinish (by omega : k ≤ n) hkcore
  have hnint := deep_core_interior hstart hfinish hk hnextcore
  have hpred : k - 1 + 1 = k := by omega
  have hv₁ : SunVertex F (R - δ) (v (k - 1)) := by
    refine ⟨v k, ?_, Or.inr hkcore⟩
    simpa [hpred] using (he (k - 1) (by omega)).1
  have hv₂ : SunVertex F (R - δ) (v (k + 2)) := by
    exact ⟨v (k + 1), by simpa [Nat.add_assoc] using adj_symm (he (k + 1) hnint.2).1,
      Or.inr hnextcore⟩
  have hleft := (deep_vertex_positions hδ he hstart hfinish (by omega) hv₁).1
  have hright := (deep_vertex_positions hδ he hstart hfinish (by omega) hv₂).2
  omega

/-- Internal vertices of a simple sun path are cores. -/
theorem internal_core
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hinj : ∀ i, i ≤ n → ∀ j, j ≤ n → v i = v j → i = j)
    {i : ℕ} (hlo : 0 < i) (hhi : i < n) : Core F R (v i) := by
  classical
  by_contra hnc
  have hl := noncore_sun_vertex_is_leaf (⟨v (i + 1), he i hhi⟩ : SunVertex F R (v i)) hnc
  have hpred : i - 1 + 1 = i := by omega
  have hp : SunAdj F R (v i) (v (i - 1)) := by
    simpa [hpred] using sunAdj_symm (he (i - 1) (by omega))
  obtain ⟨w, hw, huniq⟩ := hl
  have heq : v (i - 1) = v (i + 1) := (huniq _ hp).trans (huniq _ (he i hhi)).symm
  have hh := hinj (i - 1) (by omega) (i + 1) (by omega) heq
  omega

theorem short_path_avoids_deeper_core (hδ : δ ≤ R)
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hinj : ∀ i, i ≤ n → ∀ j, j ≤ n → v i = v j → i = j)
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    (hshort : n ≤ 4 * δ + 2) {i : ℕ} (hi : i ≤ n) : ¬ Core F (R - δ) (v i) := by
  intro hc
  have := deep_core_forces_length hδ he hinj hstart hfinish hi hc
  omega

/-- Every actual edge except the two endpoint prongs belongs to the collar. -/
theorem trimmed_edge {d : ℕ} (hd : d + 1 ≤ R)
    (he : ∀ i, i < n → SunAdj F R (v i) (v (i + 1)))
    (hinj : ∀ i, i ≤ n → ∀ j, j ≤ n → v i = v j → i = j)
    (hstart : Leaf F R (v 0)) (hfinish : Leaf F R (v n))
    (hshort : n ≤ 4 * (d + 1) + 2) {i : ℕ} (hlo : 0 < i) (hhi : i + 1 < n) :
    CollarEdge F R d (v i) (v (i + 1)) := by
  refine ⟨he i (by omega), ?_, internal_core he hinj hlo (by omega),
    internal_core he hinj (by omega) hhi⟩
  intro hdeep
  exact hdeep.2.elim
    (short_path_avoids_deeper_core hd he hinj hstart hfinish hshort (by omega))
    (short_path_avoids_deeper_core hd he hinj hstart hfinish hshort (by omega))

end IndexedConfinement

/-- Literal list adjacency at any valid index. -/
theorem listWalk_getD {E : Vertex → Vertex → Prop} {vs : List Vertex}
    (h : ListWalk E vs) {i : ℕ} (hi : i + 1 < vs.length) (default : Vertex) :
    E (vs.getD i default) (vs.getD (i + 1) default) := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases rest with
    | nil => simp at hi
    | cons b tail =>
      cases i with
      | zero => simpa using h.1
      | succ i =>
        simpa using ih h.2 (by simpa using hi : i + 1 < (b :: tail).length)

namespace BoundaryPath

/-- Total indexing; theorems only use indices on the actual traversal. -/
def vertex {F : Rectangle} {R : ℕ} (p : BoundaryPath F R) (i : ℕ) : Vertex :=
  p.vertices.getD i (.a 0 0)

theorem vertices_length {F : Rectangle} {R : ℕ} (p : BoundaryPath F R) :
    p.vertices.length = p.length + 1 := by
  have := RootedKP.AKLT.boundaryPath_length_ge_three p
  unfold length at *
  omega

theorem at_start {F : Rectangle} {R : ℕ} (p : BoundaryPath F R) : p.vertex 0 = p.start := by
  simp only [vertex, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, p.head_eq,
    Option.getD_some]

theorem at_finish {F : Rectangle} {R : ℕ} (p : BoundaryPath F R) :
    p.vertex p.length = p.finish := by
  have hh := p.last_eq
  rw [List.getLast?_eq_getElem?] at hh
  simp only [vertex, length, List.getD_eq_getElem?_getD, hh, Option.getD_some]

theorem at_adjacent {F : Rectangle} {R : ℕ} (p : BoundaryPath F R)
    (i : ℕ) (hi : i < p.length) : SunAdj F R (p.vertex i) (p.vertex (i + 1)) := by
  exact listWalk_getD p.consecutive (by have := p.vertices_length; omega) _

theorem at_injective {F : Rectangle} {R : ℕ} (p : BoundaryPath F R)
    (i : ℕ) (hi : i ≤ p.length) (j : ℕ) (hj : j ≤ p.length)
    (heq : p.vertex i = p.vertex j) : i = j := by
  have hvi : i < p.vertices.length := by have := p.vertices_length; omega
  have hvj : j < p.vertices.length := by have := p.vertices_length; omega
  simp only [vertex, List.getD_eq_getElem _ _ hvi, List.getD_eq_getElem _ _ hvj] at heq
  exact p.nodup.getElem_inj_iff.mp heq

/-- A literal simple boundary path that visits a deeper core has length at
least `4δ+3`, proved directly from its actual list and leaf endpoints. -/
theorem deeper_core_forces_length {F : Rectangle} {R δ : ℕ}
    (p : BoundaryPath F R) (hδ : δ ≤ R) {i : ℕ} (hi : i ≤ p.length)
    (hc : Core F (R - δ) (p.vertex i)) : 4 * δ + 3 ≤ p.length := by
  exact IndexedConfinement.deep_core_forces_length hδ p.at_adjacent p.at_injective
    (by simpa [p.at_start] using p.start_leaf)
    (by simpa [p.at_finish] using p.finish_leaf) hi hc

/-- Trimming both endpoint prongs of a short literal path leaves only actual
collar edges. -/
theorem trimmed_edge_in_collar {F : Rectangle} {R d : ℕ}
    (p : BoundaryPath F R) (hd : d + 1 ≤ R)
    (hshort : p.length ≤ 4 * (d + 1) + 2) {i : ℕ}
    (hlo : 0 < i) (hhi : i + 1 < p.length) :
    CollarEdge F R d (p.vertex i) (p.vertex (i + 1)) := by
  exact IndexedConfinement.trimmed_edge hd p.at_adjacent p.at_injective
    (by simpa [p.at_start] using p.start_leaf)
    (by simpa [p.at_finish] using p.finish_leaf) hshort hlo hhi

/-- Paper's automatic collar width for short even boundary paths. -/
theorem short_even_trimmed_edge {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {i : ℕ} (hlo : 0 < i) (hhi : i + 1 < p.length) :
    CollarEdge F 200 (p.length / 4 - 1) (p.vertex i) (p.vertex (i + 1)) := by
  apply p.trimmed_edge_in_collar <;> omega

/-- The checked global retraction contracts every edge of the trimmed
literal short even path. -/
theorem short_even_retraction_contracts {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {i : ℕ} (hlo : 0 < i) (hhi : i + 1 < p.length) :
    collarMap F (p.length / 4 - 1) (p.vertex i) =
      collarMap F (p.length / 4 - 1) (p.vertex (i + 1)) ∨
    Adj (collarMap F (p.length / 4 - 1) (p.vertex i))
      (collarMap F (p.length / 4 - 1) (p.vertex (i + 1))) := by
  exact collarMap_contracts_actual_edge (by omega) (by omega)
    (p.short_even_trimmed_edge hmin hmax heven hlo hhi)

/-- Every vertex of the trimmed path maps to the actual union of inner
boundary zigzags. -/
theorem short_even_retraction_in_inner {F : Rectangle} (p : BoundaryPath F 200)
    (hmin : 8 ≤ p.length) (hmax : p.length ≤ 20) (heven : p.length % 2 = 0)
    {i : ℕ} (hlo : 0 < i) (hhi : i < p.length) :
    InnerBoundary F (p.length / 4 - 1) (collarMap F (p.length / 4 - 1) (p.vertex i)) := by
  apply collarMap_image_inner (by omega)
  by_cases hi : i + 1 < p.length
  · obtain ⟨j, hj, _⟩ := collar_edge_cell_cover (by omega) (by omega)
      (p.short_even_trimmed_edge hmin hmax heven hlo hi)
    exact ⟨j, hj⟩
  · have hp : i - 1 + 1 = i := by omega
    obtain ⟨j, _, hj⟩ := collar_edge_cell_cover (by omega) (by omega)
      (p.short_even_trimmed_edge hmin hmax heven (by omega : 0 < i - 1) (by omega))
    exact ⟨j, by simpa [hp] using hj⟩

end BoundaryPath
end RootedKP.Honeycomb
