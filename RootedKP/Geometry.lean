import RootedKP.Honeycomb
import Mathlib.Tactic.SplitIfs

/-!
Proved geometric building blocks for the collar argument. In particular,
`localMap_contracts` is an unconditional theorem about the actual infinite
honeycomb graph. The global six-cell coverage/gluing and the polymer-count
consequence are separate obligations; they are not postulated here.
-/
namespace RootedKP.Honeycomb

def RectangleFace (F : Rectangle) (f : Face) : Prop :=
  F.qmin ≤ f.1 ∧ f.1 ≤ F.qmax ∧ F.rmin ≤ f.2 ∧ f.2 ≤ F.rmax

def HexBall (s : ℕ) (f : Face) : Prop :=
  -(s : ℤ) ≤ f.1 ∧ f.1 ≤ s ∧ -(s : ℤ) ≤ f.2 ∧ f.2 ≤ s ∧
    -(s : ℤ) ≤ f.1 + f.2 ∧ f.1 + f.2 ≤ s

def MinkowskiHalo (F : Rectangle) (s : ℕ) (f : Face) : Prop :=
  ∃ x y : Face, RectangleFace F x ∧ HexBall s y ∧
    f = (x.1 + y.1, x.2 + y.2)

/-- Integer intervals have no holes in their sum. -/
theorem integer_interval_sum {a b c d z : ℤ}
    (hab : a ≤ b) (hcd : c ≤ d) (hl : a + c ≤ z) (hu : z ≤ b + d) :
    ∃ x y : ℤ, a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ∧ x + y = z := by
  refine ⟨max a (z - d), z - max a (z - d), ?_⟩
  simp only [max_def]
  split_ifs <;> omega

theorem integer_interval_sum_intersection {a b c d lo hi : ℤ}
    (hab : a ≤ b) (hcd : c ≤ d) (hlh : lo ≤ hi)
    (hl : a + c ≤ hi) (hu : lo ≤ b + d) :
    ∃ x y : ℤ, a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ∧ lo ≤ x + y ∧ x + y ≤ hi := by
  have hzlo : a + c ≤ max lo (a + c) := le_max_right _ _
  have hzup : max lo (a + c) ≤ b + d := by
    simp only [max_def]
    split_ifs <;> omega
  obtain ⟨x, y, hax, hxb, hcy, hyd, hsum⟩ := integer_interval_sum hab hcd hzlo hzup
  refine ⟨x, y, hax, hxb, hcy, hyd, ?_, ?_⟩
  · rw [hsum]
    exact le_max_left _ _
  · rw [hsum]
    simp only [max_def]
    split_ifs <;> omega

/-- The six coordinate bounds are exactly the integer Minkowski sum in the
paper, not a relaxation of it. This holds for degenerate index rectangles too. -/
theorem faceHalo_iff_minkowski (F : Rectangle) (s : ℕ) (f : Face) :
    FaceHalo F s f ↔ MinkowskiHalo F s f := by
  constructor
  · intro hf
    have hq := F.q_order
    have hr := F.r_order
    have hbounds :
        max (-(s : ℤ)) (f.1 - F.qmax) ≤ min (s : ℤ) (f.1 - F.qmin) ∧
        max (-(s : ℤ)) (f.2 - F.rmax) ≤ min (s : ℤ) (f.2 - F.rmin) ∧
        max (-(s : ℤ)) (f.1 - F.qmax) +
          max (-(s : ℤ)) (f.2 - F.rmax) ≤ s ∧
        -(s : ℤ) ≤ min (s : ℤ) (f.1 - F.qmin) + min (s : ℤ) (f.2 - F.rmin) := by
      unfold FaceHalo at hf
      simp only [max_def, min_def]
      split_ifs <;> omega
    obtain ⟨x, y, hlx, hxu, hly, hyu, hls, hsu⟩ :=
      integer_interval_sum_intersection hbounds.1 hbounds.2.1
        (show -(s : ℤ) ≤ s by omega) hbounds.2.2.1 hbounds.2.2.2
    refine ⟨(f.1 - x, f.2 - y), (x, y), ?_, ?_, ?_⟩
    · simp only [RectangleFace]
      simp only [max_def, min_def] at hlx hxu hly hyu
      split_ifs at * <;> omega
    · simp only [HexBall]
      simp only [max_def, min_def] at hlx hxu hly hyu
      split_ifs at * <;> omega
    · apply Prod.ext <;> simp
  · rintro ⟨⟨xq, xr⟩, ⟨yq, yr⟩, hx, hy, rfl⟩
    simp only [RectangleFace] at hx
    simp only [HexBall] at hy
    simp only [FaceHalo]
    omega

/-- Both faces bordering an edge are included. The three alternatives
list the exact two incident faces for the three possible edge directions. -/
def TwoFaceAdj (F : Rectangle) (s : ℕ) : Vertex → Vertex → Prop
  | .a q r, .b q' r' =>
      ((q' = q ∧ r' = r) ∧ FaceHalo F s (q + 1, r) ∧ FaceHalo F s (q, r + 1)) ∨
      ((q' = q - 1 ∧ r' = r) ∧ FaceHalo F s (q, r) ∧ FaceHalo F s (q, r + 1)) ∨
      ((q' = q ∧ r' = r - 1) ∧ FaceHalo F s (q, r) ∧ FaceHalo F s (q + 1, r))
  | .b q' r', .a q r =>
      ((q' = q ∧ r' = r) ∧ FaceHalo F s (q + 1, r) ∧ FaceHalo F s (q, r + 1)) ∨
      ((q' = q - 1 ∧ r' = r) ∧ FaceHalo F s (q, r) ∧ FaceHalo F s (q, r + 1)) ∨
      ((q' = q ∧ r' = r - 1) ∧ FaceHalo F s (q, r) ∧ FaceHalo F s (q + 1, r))
  | _, _ => False

/-- Parallel enlargement preserves every face. -/
theorem faceHalo_mono {F : Rectangle} {s t : ℕ} (hst : s ≤ t) {f : Face}
    (h : FaceHalo F s f) : FaceHalo F t f := by
  unfold FaceHalo at *
  omega

theorem core_mono {F : Rectangle} {s t : ℕ} (hst : s ≤ t) {v : Vertex}
    (h : Core F s v) : Core F t v := by
  obtain ⟨f, hf, hv⟩ := h
  exact ⟨f, faceHalo_mono hst hf, hv⟩

theorem sunAdj_mono {F : Rectangle} {s t : ℕ} (hst : s ≤ t) {u v : Vertex}
    (h : SunAdj F s u v) : SunAdj F t u v := by
  exact ⟨h.1, h.2.elim (fun hu => Or.inl (core_mono hst hu))
    (fun hv => Or.inr (core_mono hst hv))⟩

/-- Exact entry-distance estimate used in short-path confinement. The height
hypothesis identifies the outer `q`-max leaf layer, while the target is an
actual vertex of the deeper sun. -/
theorem approach_deeper_sun {F : Rectangle} {R δ n : ℕ} (hδ : δ ≤ R)
    {x y : Vertex} (hwalk : Walk x y n)
    (hx : heightQ x = 2 * (F.qmax + R) + 2)
    (hy : SunVertex F (R - δ) y) : 2 * δ ≤ n := by
  have hupper := sun_heightQ_upper hy
  have hdist := hwalk.height_bounds heightQ_lipschitz
  omega

/-- Once both approaches and the inner component are identified, a short
path cannot use the deeper sun. The decomposition hypotheses remain explicit. -/
theorem confinement_length_contradiction {n δ p m s : ℕ}
    (hn : n ≤ 4 * δ + 2) (hp : 2 * δ ≤ p) (hm : 3 ≤ m)
    (hs : 2 * δ ≤ s) (hlen : n = p + m + s) : False := by
  omega

/-- Integer arclength coordinate of a vertex on a vertical side zigzag. -/
def vertexAt (Q τ : ℤ) : Vertex :=
  if τ % 2 = 0 then .a Q (τ / 2) else .b Q ((τ - 1) / 2)

theorem vertexAt_height (Q τ : ℤ) : heightR (vertexAt Q τ) = τ := by
  unfold vertexAt
  split <;> simp only [heightR] <;> omega

theorem vertexAt_even (Q r : ℤ) : vertexAt Q (2 * r) = .a Q r := by
  unfold vertexAt
  split <;> first | congr 1 <;> omega | omega

theorem vertexAt_odd (Q r : ℤ) : vertexAt Q (2 * r + 1) = .b Q r := by
  unfold vertexAt
  split <;> first | congr 1 <;> omega | omega

theorem vertexAt_adjacent (Q τ : ℤ) : Adj (vertexAt Q τ) (vertexAt Q (τ + 1)) := by
  by_cases h : τ % 2 = 0
  · have h' : (τ + 1) % 2 ≠ 0 := by omega
    simp [vertexAt, h, h', Adj]
  · have h' : (τ + 1) % 2 = 0 := by omega
    simp only [vertexAt, if_neg h, if_pos h', Adj]
    right
    right
    exact ⟨trivial, by omega⟩

theorem vertexAt_contracts (Q x y : ℤ) (hxy : x - y ≤ 1) (hyx : y - x ≤ 1) :
    vertexAt Q x = vertexAt Q y ∨ Adj (vertexAt Q x) (vertexAt Q y) := by
  by_cases h : x = y
  · exact Or.inl (congrArg (vertexAt Q) h)
  · right
    have hcases : y = x + 1 ∨ x = y + 1 := by omega
    rcases hcases with rfl | h'
    · exact vertexAt_adjacent Q x
    · rw [h']
      exact adj_symm (vertexAt_adjacent Q y)

def clamp (lo hi x : ℤ) : ℤ := max lo (min hi x)

theorem clamp_mem {lo hi x : ℤ} (h : lo ≤ hi) :
    lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

theorem clamp_of_mem {lo hi x : ℤ} (hl : lo ≤ x) (hu : x ≤ hi) :
    clamp lo hi x = x := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

theorem clamp_of_below {lo hi x : ℤ} (hx : x ≤ lo) : clamp lo hi x = lo := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

theorem clamp_of_above {lo hi x : ℤ} (h : lo ≤ hi) (hx : hi ≤ x) :
    clamp lo hi x = hi := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

theorem clamp_contracts (lo hi x y : ℤ) (hxy : x - y ≤ 1) (hyx : y - x ≤ 1) :
    clamp lo hi x - clamp lo hi y ≤ 1 ∧
      clamp lo hi y - clamp lo hi x ≤ 1 := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> omega

/-- The exact clamp map of equation (A.2), in one rotated side chart. -/
def localMap (Q r₀ r₁ : ℤ) (d : ℕ) (v : Vertex) : Vertex :=
  vertexAt (Q - d) (clamp (2 * (r₀ + d) - 1) (2 * r₁) (heightR v))

/-- The local clamp sends every ambient edge to an inner-side edge or a point.
Cell membership is not needed for this local fact. -/
theorem localMap_contracts (Q r₀ r₁ : ℤ) (d : ℕ) {u v : Vertex}
    (huv : Adj u v) :
    localMap Q r₀ r₁ d u = localMap Q r₀ r₁ d v ∨
      Adj (localMap Q r₀ r₁ d u) (localMap Q r₀ r₁ d v) := by
  have h := heightR_lipschitz u v huv
  have hc := clamp_contracts (2 * (r₀ + d) - 1) (2 * r₁)
    (heightR u) (heightR v) h.2 h.1
  exact vertexAt_contracts (Q - d) _ _ hc.1 hc.2

theorem localMap_fixes_inner (Q r₀ r₁ τ : ℤ) (d : ℕ)
    (hl : 2 * (r₀ + d) - 1 ≤ τ) (hu : τ ≤ 2 * r₁) :
    localMap Q r₀ r₁ d (vertexAt (Q - d) τ) = vertexAt (Q - d) τ := by
  simp only [localMap, vertexAt_height, clamp_of_mem hl hu]

/-- All `b` vertices on the left connector have the same image. -/
theorem localMap_left_b (Q r₀ r₁ : ℤ) (d j : ℕ) (hj : j ≤ d) :
    localMap Q r₀ r₁ d (.b (Q - j) (r₀ + j - 1)) =
      vertexAt (Q - d) (2 * (r₀ + d) - 1) := by
  unfold localMap
  rw [clamp_of_below]
  simp only [heightR]
  omega

/-- The intermediate `a` vertices on the left connector have the same image. -/
theorem localMap_left_a (Q r₀ r₁ : ℤ) (d j : ℕ) (hj : j < d) :
    localMap Q r₀ r₁ d (.a (Q - j) (r₀ + j)) =
      vertexAt (Q - d) (2 * (r₀ + d) - 1) := by
  unfold localMap
  rw [clamp_of_below]
  simp only [heightR]
  omega

theorem localMap_right_a (Q r₀ r₁ : ℤ) (d j : ℕ)
    (h : 2 * (r₀ + d) - 1 ≤ 2 * r₁) :
    localMap Q r₀ r₁ d (.a (Q - j) r₁) = vertexAt (Q - d) (2 * r₁) := by
  unfold localMap
  rw [clamp_of_above h]
  simp only [heightR]

  omega

theorem localMap_right_b (Q r₀ r₁ : ℤ) (d j : ℕ)
    (h : 2 * (r₀ + d) - 1 ≤ 2 * r₁) :
    localMap Q r₀ r₁ d (.b (Q - j - 1) r₁) = vertexAt (Q - d) (2 * r₁) := by
  unfold localMap
  rw [clamp_of_above h]
  simp only [heightR]
  omega

/-- The neighboring chart's outer left endpoint is exactly the current
chart's outer right endpoint, with the correct bipartite phase. -/
theorem rotated_outer_connector_endpoint (Q S : ℤ) :
    rotate (.b S (-Q - 1)) = .a Q (S - Q) := by
  simp only [rotate]
  congr 1 <;> omega

theorem rotated_inner_connector_endpoint (Q S : ℤ) (d : ℕ) :
    rotate (.b (S - d) (-Q + d - 1)) = .a (Q - d) (S - Q) := by
  simp only [rotate]
  congr 1 <;> omega

/-- First edge of the rotated neighboring left connector. -/
theorem rotated_connector_intermediate (Q S : ℤ) (j : ℕ) :
    rotate (.a (S - j) (-Q + j)) = .b (Q - j - 1) (S - Q) := by
  simp only [rotate]
  congr 1 <;> omega

end RootedKP.Honeycomb
