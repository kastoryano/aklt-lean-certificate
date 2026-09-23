import RootedKP.Arithmetic

/-!
Exact convolution of the endpoint counting envelope. The first nine values
are 1,2,2,4,6,8,16,24,40; beyond them the envelope is 2^k/16.
This file proves the algebraic convolution identity for every n≥21. A separate
geometric/enumeration theorem must establish that actual endpoint paths are
bounded by this envelope.
-/
namespace RootedKP.EndpointConvolution
open scoped BigOperators
set_option maxHeartbeats 0

def normalized (k : ℕ) : ℚ :=
  match k with
  | 1 => 1/2
  | 2 => 1/2
  | 3 => 1/4
  | 4 => 1/4
  | 5 => 3/16
  | 6 => 1/8
  | 7 => 1/8
  | 8 => 3/32
  | 9 => 5/64
  | _ => 1/16

def endpointEnvelope (k : ℕ) : ℚ := 2 ^ k * normalized k

theorem first_nine_values :
    (List.range 9).map (fun k => endpointEnvelope (k+1)) =
      [1,2,2,4,6,8,16,24,40] := by
  norm_num [List.range_succ, endpointEnvelope, normalized]

theorem normalized_long (k : ℕ) (hk : 10 ≤ k) : normalized k = 1/16 := by
  unfold normalized
  split <;> first | rfl | omega

theorem envelope_long (k : ℕ) (hk : 10 ≤ k) : endpointEnvelope k = 2 ^ k / 16 := by
  rw [endpointEnvelope, normalized_long k hk]
  ring

theorem normalized_first_nine :
    (∑ i ∈ Finset.range 9, normalized (i+1) * (1/16)) = 135/1024 := by
  norm_num [Finset.sum_range_succ, normalized]

theorem normalized_last_nine :
    (∑ i ∈ Finset.range 9, (1/16) * normalized (9-i)) = 135/1024 := by
  norm_num [Finset.sum_range_succ, normalized]

theorem normalized_convolution (n : ℕ) (hn : 21 ≤ n) :
    (∑ i ∈ Finset.range (n-2), normalized (i+1) * normalized (n-2-i)) =
      (2 * (n : ℚ) + 95) / 512 := by
  have hsplit : n-2 = (9 + (n-20)) + 9 := by omega
  nth_rw 1 [hsplit]
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have hleft : (∑ i ∈ Finset.range 9,
      normalized (i+1) * normalized (n-2-i)) = 135/1024 := by
    convert normalized_first_nine using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [normalized_long (n-2-i) (by omega)]
  have hmiddle : (∑ i ∈ Finset.range (n-20),
      normalized (9+i+1) * normalized (n-2-(9+i))) = (n-20 : ℕ) / (256 : ℚ) := by
    calc
      _ = ∑ _i ∈ Finset.range (n-20), (1/256 : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [normalized_long _ (by omega), normalized_long _ (by omega)]
        norm_num
      _ = _ := by simp; ring
  have hright : (∑ i ∈ Finset.range 9,
      normalized (9+(n-20)+i+1) * normalized (n-2-(9+(n-20)+i))) = 135/1024 := by
    convert normalized_last_nine using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [normalized_long _ (by omega)]
    congr 2
    omega
  rw [hleft, hmiddle, hright]
  rw [Nat.cast_sub (by omega : 20 ≤ n)]
  norm_num
  ring

/-- The two endpoints and middle plateau give the exact coefficient 2n+95. -/
theorem endpoint_convolution (n : ℕ) (hn : 21 ≤ n) :
    (∑ i ∈ Finset.range (n-2), endpointEnvelope (i+1) * endpointEnvelope (n-2-i)) =
      (2 * (n : ℚ) + 95) * 2 ^ n / 1024 := by
  calc
    _ = ∑ i ∈ Finset.range (n-2),
        2 ^ (n-1) * (normalized (i+1) * normalized (n-2-i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hex : i+1+(n-2-i) = n-1 := by omega
      unfold endpointEnvelope
      rw [show (2:ℚ)^(i+1) * normalized (i+1) *
          ((2:ℚ)^(n-2-i) * normalized (n-2-i)) =
          ((2:ℚ)^(i+1) * 2^(n-2-i)) *
          (normalized (i+1) * normalized (n-2-i)) by ring, ← pow_add, hex]
    _ = 2 ^ (n-1) * ((2 * (n : ℚ) + 95) / 512) := by
      rw [← Finset.mul_sum, normalized_convolution n hn]
    _ = _ := by
      have hp : (2 : ℚ)^n = 2^(n-1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hp]
      ring

theorem endpointEnvelope_nonneg (k : ℕ) : 0 ≤ endpointEnvelope k := by
  unfold endpointEnvelope normalized
  split <;> positivity

/-- Any actual nonnegative integer count sequence satisfying the endpoint
envelope inherits the exact convolution upper bound. -/
theorem count_convolution_le (c : ℕ → ℕ)
    (hc : ∀ k, 1 ≤ k → (c k : ℚ) ≤ endpointEnvelope k)
    (n : ℕ) (hn : 21 ≤ n) :
    (∑ i ∈ Finset.range (n-2), (c (i+1) : ℚ) * (c (n-2-i) : ℚ)) ≤
      (2 * (n : ℚ) + 95) * 2 ^ n / 1024 := by
  rw [← endpoint_convolution n hn]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul (hc _ (by omega)) (hc _ (by omega))
    (Nat.cast_nonneg _) (endpointEnvelope_nonneg _)

end RootedKP.EndpointConvolution
#print axioms RootedKP.EndpointConvolution.endpoint_convolution

#print axioms RootedKP.EndpointConvolution.count_convolution_le
