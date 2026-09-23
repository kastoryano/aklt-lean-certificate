import RootedKP.BoundaryCoordinates

namespace RootedKP.Honeycomb.BoundaryCycle
set_option maxHeartbeats 1000000

/-- The cumulative number of collapsed edges never decreases along the
outer boundary's linear indexing. -/
theorem retraction_loss_monotone (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F 0 i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F 0 j ≤ σ) (hσ₁ : σ < upper F j)
    (horder : coordinate F 0 i τ ≤ coordinate F 0 j σ) :
    coordinate F 0 i τ - coordinate F d i (clamp (lower F d i) (upper F i) τ) ≤
      coordinate F 0 j σ - coordinate F d j (clamp (lower F d j) (upper F j) σ) := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;>
    simp only [coordinate, offset, baseLength, width, height, lower, upper, sideChart,
      clamp, max_def, min_def] at hτ₀ hτ₁ hσ₀ hσ₁ horder ⊢ <;>
    split_ifs <;> omega

/-- The explicit retraction preserves the linear order of outer points. -/
theorem retraction_coordinate_monotone (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F 0 i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F 0 j ≤ σ) (hσ₁ : σ < upper F j)
    (horder : coordinate F 0 i τ ≤ coordinate F 0 j σ) :
    coordinate F d i (clamp (lower F d i) (upper F i) τ) ≤
      coordinate F d j (clamp (lower F d j) (upper F j) σ) := by
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;>
    simp only [coordinate, offset, baseLength, width, height, lower, upper, sideChart,
      clamp, max_def, min_def] at hτ₀ hτ₁ hσ₀ hσ₁ horder ⊢ <;>
    split_ifs <;> omega

theorem perimeter_loss (F : Rectangle) (d : ℕ) :
    perimeter F 0 = perimeter F d + 12 * d := by
  dsimp only [perimeter, baseLength]
  omega

/-- Crossing the indexing cut still costs only `12d`, because the cumulative
loss at the earlier outer endpoint is no larger than at the later one. -/
theorem preimage_wrapping_arc_length (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F 0 i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F 0 j ≤ σ) (hσ₁ : σ < upper F j)
    (horder : coordinate F 0 j σ ≤ coordinate F 0 i τ) :
    perimeter F 0 - coordinate F 0 i τ + coordinate F 0 j σ ≤
      perimeter F d - coordinate F d i (clamp (lower F d i) (upper F i) τ) +
        coordinate F d j (clamp (lower F d j) (upper F j) σ) + 12 * d := by
  have hm := retraction_loss_monotone F hd j i σ τ hσ₀ hσ₁ hτ₀ hτ₁ horder
  have hp := perimeter_loss F d
  omega


/-- Lift outer coordinates using a cut on the image circle. The same
predicate selects the corresponding lift of the image coordinate. -/
def liftOuter (F : Rectangle) (d : ℕ) (cut : ℤ) (i : Fin 6) (τ : ℤ) : ℤ :=
  if coordinate F d i (clamp (lower F d i) (upper F i) τ) < cut
  then coordinate F 0 i τ + perimeter F 0 else coordinate F 0 i τ

def liftImage (F : Rectangle) (d : ℕ) (cut : ℤ) (i : Fin 6) (τ : ℤ) : ℤ :=
  if coordinate F d i (clamp (lower F d i) (upper F i) τ) < cut
  then coordinate F d i (clamp (lower F d i) (upper F i) τ) + perimeter F d
  else coordinate F d i (clamp (lower F d i) (upper F i) τ)

/-- For every cut, the spread of cumulative losses is at most `12d`.
This accounts for collapsed endpoint fibers and arcs crossing the old cut. -/
theorem lifted_loss_spread (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (cut : ℤ)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F 0 i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F 0 j ≤ σ) (hσ₁ : σ < upper F j) :
    (liftOuter F d cut i τ - liftImage F d cut i τ) -
      (liftOuter F d cut j σ - liftImage F d cut j σ) ≤ 12 * d := by
  have hi := retraction_coordinate_loss F hd i hτ₀ hτ₁
  have hj := retraction_coordinate_loss F hd j hσ₀ hσ₁
  have hp := perimeter_loss F d
  dsimp only at hi hj
  by_cases hx : coordinate F 0 i τ ≤ coordinate F 0 j σ
  · have hm := retraction_coordinate_monotone F hd i j τ σ hτ₀ hτ₁ hσ₀ hσ₁ hx
    have hl := retraction_loss_monotone F hd i j τ σ hτ₀ hτ₁ hσ₀ hσ₁ hx
    unfold liftOuter liftImage
    split_ifs <;> omega
  · have hx' : coordinate F 0 j σ ≤ coordinate F 0 i τ := by omega
    have hm := retraction_coordinate_monotone F hd j i σ τ hσ₀ hσ₁ hτ₀ hτ₁ hx'
    have hl := retraction_loss_monotone F hd j i σ τ hσ₀ hσ₁ hτ₀ hτ₁ hx'
    unfold liftOuter liftImage
    split_ifs <;> omega

/-- The full preimage of an inner arc, unwrapped at any chosen cut, has
pairwise extent at most the arc length plus `12d`. -/
theorem arc_preimage_extent (F : Rectangle) {d : ℕ} (hd : d ≤ 4) (cut lo hi : ℤ)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F 0 i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F 0 j ≤ σ) (hσ₁ : σ < upper F j)
    (hiImage : liftImage F d cut i τ ≤ hi)
    (hjImage : lo ≤ liftImage F d cut j σ) :
    liftOuter F d cut i τ - liftOuter F d cut j σ ≤ hi - lo + 12 * d := by
  have hh := lifted_loss_spread F hd cut i j τ σ hτ₀ hτ₁ hσ₀ hσ₁
  omega

end RootedKP.Honeycomb.BoundaryCycle
