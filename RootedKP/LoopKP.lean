import RootedKP.LoopMass
import RootedKP.LoopOverlap

/-!
The entire loop part of the literal AKLT KP bound, for canonical regional
polymers. Every incompatible loop is charged to a core edge of the root.
There are at most length−2 such edges for a boundary path and at most length
for a loop. The edge mass is supplied by verified enumeration and an analytic
tail, so this theorem has no counting or geometric hypothesis.
-/
namespace RootedKP.AKLT
open Honeycomb
set_option maxHeartbeats 0

/-- Unconditional loop contribution to the seven-class scalar KP accounting. -/
theorem loop_kindMass_le_allowance (F : Rectangle) (p : Polymer F) :
    kindMass p .loop ≤ (loopAllowance p : ℝ) := by
  have hcover := loop_mass_le_edge_cover p p.eligibleEdges (by
    intro q hq hi
    exact p.incompatible_loop_shared_eligible_edge q hq
      ((Polymer.incompatible_symm q p).mp hi))
  have hnonneg : (0 : ℝ) ≤ (Arithmetic.loopMass : ℝ) := by
    exact_mod_cast loopMass_nonneg
  apply hcover.trans
  cases hk : p.kind with
  | path =>
    have hcard : (p.eligibleEdges.card : ℝ) ≤ (p.length : ℝ) - 2 := by
      have hn := p.path_length_ge_three hk
      have hc := p.eligibleEdges_card_path hk
      have hr : (p.eligibleEdges.card : ℝ) ≤ ((p.length - 2 : ℕ) : ℝ) := by
        exact_mod_cast hc
      simpa only [Nat.cast_sub (by omega : 2 ≤ p.length), Nat.cast_ofNat] using hr
    simpa [loopAllowance, hk] using mul_le_mul_of_nonneg_right hcard hnonneg
  | loop =>
    have hcard : (p.eligibleEdges.card : ℝ) ≤ (p.length : ℝ) := by
      exact_mod_cast p.eligibleEdges_card_loop
    simpa [loopAllowance, hk] using mul_le_mul_of_nonneg_right hcard hnonneg

end RootedKP.AKLT
#print axioms RootedKP.AKLT.loop_kindMass_le_allowance
