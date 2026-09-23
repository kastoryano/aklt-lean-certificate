import RootedKP.PathTailEdges
import RootedKP.PathOverlap

/-! The infinite boundary-path tail estimate is unconditional for all actual
radius-200 regional polymers. The only numerical inputs are the kernel-checked
N1--N10 endpoint certificates and their proved continuation bound. -/
namespace RootedKP.AKLT
open Honeycomb
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

/-- Complete canonical lengthwise tail count, with the two leaf prongs
charged jointly and all remaining shared edges charged by convolution. -/
theorem tail_length_count_bound : TailLengthCountBound := by
  intro F p n hn
  have h := path_length_count_le_edge_charges p n hn (by
    intro q hq
    have hi := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.2
    exact p.incompatible_shared_edge q ((Polymer.incompatible_symm q p).mp hi))
  have hA : 0 ≤ (2*(n:ℝ)+95)*2^n/1024 := by positivity
  have hB : 0 ≤ (2:ℝ)^n/32 := by positivity
  apply h.trans
  cases hk : p.kind with
  | path =>
    have hlen := p.path_length_ge_three hk
    have hc : (p.eligibleEdges.card : ℝ) ≤ (p.length:ℝ)-2 := by
      have hh : (p.eligibleEdges.card : ℝ) ≤ ((p.length-2:ℕ):ℝ) := by
        exact_mod_cast p.eligibleEdges_card_path hk
      simpa only [Nat.cast_sub (by omega : 2≤p.length),Nat.cast_ofNat] using hh
    have hb : ((p.edges \ p.eligibleEdges).card : ℝ) ≤ 2 := by
      exact_mod_cast p.noneligibleEdges_card_path hk
    have hh := add_le_add (mul_le_mul_of_nonneg_right hc hA)
      (mul_le_mul_of_nonneg_right hb hB)
    apply hh.trans_eq
    simp only [boundaryCharge,internalCharge,hk,ite_true]
    ring
  | loop =>
    have hc : (p.eligibleEdges.card : ℝ) ≤ (p.length:ℝ) := by
      exact_mod_cast p.eligibleEdges_card_loop
    have hb := p.noneligibleEdges_card_loop hk
    rw [hb, Nat.cast_zero, zero_mul, add_zero]
    apply (mul_le_mul_of_nonneg_right hc hA).trans_eq
    simp only [boundaryCharge,internalCharge,hk,show Kind.loop ≠ Kind.path by decide,ite_false]
    ring

/-- The complete weighted infinite tail, ready for PathCountingInputs.tails. -/
theorem regional_path_tail_bound (F : Rectangle) (p : Polymer F) :
    tailPathEnvelope p ≤ (tailEnvelopeAllowance p : ℝ) :=
  tail_allowance_of_length_counts tail_length_count_bound F p

end
end RootedKP.AKLT
#print axioms RootedKP.AKLT.tail_length_count_bound
#print axioms RootedKP.AKLT.regional_path_tail_bound
