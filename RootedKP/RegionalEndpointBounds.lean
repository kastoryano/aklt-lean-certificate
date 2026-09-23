import RootedKP.RegionalEndpointGrowth
import RootedKP.BoundaryPrefixGlobal
import RootedKP.EndpointConvolution

/-! Unconditional endpoint bounds for every actual radius-200 regional sun. -/
namespace RootedKP.RegionalEndpoints
open Honeycomb BoundaryCounts EndpointConvolution
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

theorem count_prefix_bound (F : Rectangle) (k : ℕ) (hlo : 1 ≤ k) (hhi : k ≤ 10)
    (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    count F k u forbidden ≤ prefixCap k := by
  obtain ⟨c⟩ := regional_chart_cover F u 10 ⟨forbidden,(mem_next F u forbidden).mp hf⟩ (by decide)
  have hforbidden : c.iso.vertex forbidden ∈ BoundaryCharts.next .corner (c.iso.vertex u) :=
    (BoundaryCharts.mem_next _ _ _).mpr
      ((c.adjacency_iff (VertexWithin.refl u 10) forbidden).mp ((mem_next F u forbidden).mp hf))
  cases k with
  | zero => omega
  | succ n =>
      exact (count_le_chart (forbidden := forbidden) c hhi).trans
        (chart_prefix_bound .corner (n+1) hlo hhi _ _ hforbidden)

theorem count_ten (F : Rectangle) (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    count F 10 u forbidden ≤ 64 := by
  simpa [prefixCap] using count_prefix_bound F 10 (by decide) (by decide) u forbidden hf

theorem count_long (F : Rectangle) (k : ℕ) (hk : 10 ≤ k)
    (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    count F k u forbidden ≤ 2 ^ (k-4) :=
  count_le_from_ten F (count_ten F) k hk u forbidden hf

/-- The complete N(k) envelope holds for actual regional endpoint paths. -/
theorem count_le_envelope (F : Rectangle) (k : ℕ) (hk : 1 ≤ k)
    (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    (count F k u forbidden : ℚ) ≤ endpointEnvelope k := by
  by_cases hshort : k ≤ 9
  · have h := count_prefix_bound F k hk (by omega) u forbidden hf
    have he : (prefixCap k : ℚ) = endpointEnvelope k := by
      interval_cases k <;> norm_num [prefixCap, endpointEnvelope, normalized]
    rw [← he]
    exact_mod_cast h
  · have hk10 : 10 ≤ k := by omega
    have h := count_long F k hk10 u forbidden hf
    have hp : (2 : ℚ)^k = 2^(k-4)*16 := by
      change (2 : ℚ)^k = 2^(k-4)*2^4
      rw [← pow_add]
      congr 1
      omega
    calc
      _ ≤ (2 : ℚ)^(k-4) := by exact_mod_cast h
      _ = endpointEnvelope k := by rw [envelope_long k hk10, hp]; ring

/-- The exact convolution constant now bounds the two actual endpoint arms
at any regional edge, without any local-chart hypothesis. -/
theorem two_arm_convolution (F : Rectangle) (n : ℕ) (hn : 21 ≤ n)
    (u v : Vertex) (hv : v ∈ next F u) :
    (∑ i ∈ Finset.range (n-2), (count F (i+1) u v : ℚ) * (count F (n-2-i) v u : ℚ)) ≤
      (2 * (n : ℚ) + 95) * 2^n / 1024 := by
  have hu : u ∈ next F v := (mem_next F v u).mpr (sunAdj_symm ((mem_next F u v).mp hv))
  rw [← endpoint_convolution n hn]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_le_mul (count_le_envelope F (i+1) (by omega) u v hv)
    (count_le_envelope F (n-2-i) (by omega) v u hu)
    (Nat.cast_nonneg _) (endpointEnvelope_nonneg _)

end
end RootedKP.RegionalEndpoints
#print axioms RootedKP.RegionalEndpoints.count_le_envelope
#print axioms RootedKP.RegionalEndpoints.two_arm_convolution
