import RootedKP.BoundaryCycle

namespace RootedKP.Honeycomb.BoundaryCycle
set_option maxHeartbeats 1000000

/-- Ambient adjacency on the literal inner-boundary vertices has no chords:
its only edges are consecutive side parameters and the six joint edges. -/
theorem adjacent_parameters (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (i j : Fin 6) (τ σ : ℤ)
    (hτ₀ : lower F d i ≤ τ) (hτ₁ : τ < upper F i)
    (hσ₀ : lower F d j ≤ σ) (hσ₁ : σ < upper F j)
    (hadj : Adj (point F d i τ) (point F d j σ)) :
    (i = j ∧ (τ + 1 = σ ∨ σ + 1 = τ)) ∨
      (j = nextSide i ∧ τ + 1 = upper F i ∧ σ = lower F d j) ∨
      (i = nextSide j ∧ σ + 1 = upper F j ∧ τ = lower F d i) := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, τ = 2*t ∨ τ = 2*t+1 := ⟨τ / 2, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : ℤ, σ = 2*s ∨ σ = 2*s+1 := ⟨σ / 2, by omega⟩
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;> fin_cases j <;> rcases ht with rfl | rfl <;> rcases hs with rfl | rfl <;>
    simp only [point, fromChart, sideChart, lower, upper, nextSide,
      vertexAt_even, vertexAt_odd, rotate, Adj] at hτ₀ hτ₁ hσ₀ hσ₁ hadj ⊢ <;>
    norm_num at * <;> omega

end RootedKP.Honeycomb.BoundaryCycle
