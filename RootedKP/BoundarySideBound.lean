import RootedKP.BoundaryCounts

/-! Same-side corner paths inject into the straight-side count. This proves
that the local per-endpoint even-path maximum needs no additional corner table.
It does not provide the rectangle-to-chart or path-parity bridge. -/

namespace RootedKP.BoundaryCounts

open Honeycomb BoundaryCharts Enumeration

/-- Injective graph maps transport the complete simple-path specification. -/
theorem extends_map {C D : Chart} (f : Vertex → Vertex) (hinj : Function.Injective f)
    (hstep : ∀ u v, BoundaryCharts.Adj C u v → BoundaryCharts.Adj D (f u) (f v))
    {n : ℕ} {trail result : List Vertex} (he : Extends (next C) n trail result) :
    Extends (next D) n (trail.map f) (result.map f) := by
  induction he with
  | refl trail => exact .refl _
  | @step u v us result n hv hnew he ih =>
    apply Extends.step ((mem_next D _ _).mpr (hstep u v ((mem_next C _ _).mp hv)))
    · intro hm
      change f v ∈ (u :: us).map f at hm
      obtain ⟨x, hx, heq⟩ := List.mem_map.mp hm
      exact hnew ((hinj heq) ▸ hx)
    · exact ih

/-- The upper corner ray becomes q=1 after swapping the two coordinates. -/
def upperToSide (q₀ : ℤ) : Vertex → Vertex
  | .a q r => .a r (q - q₀)
  | .b q r => .b r (q - q₀)

/-- Inversion and a one-cell shift put the left corner ray on q=1. -/
def leftToSide (r₀ : ℤ) : Vertex → Vertex
  | .a q r => .b (-q - 1) (r₀ - r)
  | .b q r => .a (-q - 1) (r₀ - r)

theorem upperToSide_injective (q₀ : ℤ) : Function.Injective (upperToSide q₀) := by
  intro u v h
  cases u <;> cases v <;> simp_all [upperToSide] <;> omega

theorem leftToSide_injective (r₀ : ℤ) : Function.Injective (leftToSide r₀) := by
  intro u v h
  cases u <;> cases v <;> simp_all [leftToSide] <;> omega

theorem upperToSide_adj (q₀ : ℤ) {u v : Vertex} (h : BoundaryCharts.Adj .corner u v) :
    BoundaryCharts.Adj .side (upperToSide q₀ u) (upperToSide q₀ v) := by
  cases u <;> cases v <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, upperToSide] <;> omega

theorem leftToSide_adj (r₀ : ℤ) {u v : Vertex} (h : BoundaryCharts.Adj .corner u v) :
    BoundaryCharts.Adj .side (leftToSide r₀ u) (leftToSide r₀ v) := by
  cases u <;> cases v <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, leftToSide] <;> omega

def upperBeyond (q₀ : ℤ) : Vertex → Prop
  | .a q r => q₀ < q ∧ r = 1
  | _ => False

def leftBeyond (r₀ : ℤ) : Vertex → Prop
  | .b q r => q = -2 ∧ r < r₀
  | _ => False

instance (q₀ : ℤ) (v : Vertex) : Decidable (upperBeyond q₀ v) := by
  cases v <;> unfold upperBeyond <;> infer_instance
instance (r₀ : ℤ) (v : Vertex) : Decidable (leftBeyond r₀ v) := by
  cases v <;> unfold leftBeyond <;> infer_instance

theorem pathsTo_card_le_of_map {C D : Chart} {accept target : Vertex → Prop}
    [DecidablePred accept] [DecidablePred target] (f : Vertex → Vertex)
    (hinj : Function.Injective f)
    (hstep : ∀ u v, BoundaryCharts.Adj C u v → BoundaryCharts.Adj D (f u) (f v))
    (hend : ∀ v, accept v → target (f v)) (n : ℕ) (start : Vertex) :
    (pathsTo C accept n start).card ≤ (pathsTo D target n (f start)).card := by
  have hsub : (pathsTo C accept n start).image (List.map f) ⊆
      pathsTo D target n (f start) := by
    intro result hm
    obtain ⟨trail, ht, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨he, ha⟩ := (mem_pathsTo_iff _ _ _ _ _).mp ht
    apply (mem_pathsTo_iff _ _ _ _ _).mpr
    refine ⟨extends_map f hinj hstep he, ?_⟩
    cases trail with
    | nil => exact False.elim ha
    | cons v vs => exact hend v ha
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (List.map_injective_iff.mpr hinj)] at hcard
  exact hcard

theorem upper_same_side_count_le (n : ℕ) (q₀ : ℤ) :
    (pathsTo .corner (upperBeyond q₀) n (.a q₀ 1)).card ≤ sideCount n := by
  rw [sideCount_eq_card]
  have h := pathsTo_card_le_of_map (accept := upperBeyond q₀) (target := sideAbove) (upperToSide q₀) (upperToSide_injective q₀)
    (fun _ _ => upperToSide_adj q₀) (fun v hv => by
      cases v <;> simp_all [upperBeyond, sideAbove, upperToSide] <;> omega) n (.a q₀ 1)
  simpa [upperToSide, sidePaths] using h

theorem left_same_side_count_le (n : ℕ) (r₀ : ℤ) :
    (pathsTo .corner (leftBeyond r₀) n (.b (-2) r₀)).card ≤ sideCount n := by
  rw [sideCount_eq_card]
  have h := pathsTo_card_le_of_map (accept := leftBeyond r₀) (target := sideAbove) (leftToSide r₀) (leftToSide_injective r₀)
    (fun _ _ => leftToSide_adj r₀) (fun v hv => by
      cases v <;> simp_all [leftBeyond, sideAbove, leftToSide] <;> omega) n (.b (-2) r₀)
  simpa [leftToSide, sidePaths] using h

end RootedKP.BoundaryCounts
