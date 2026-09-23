import RootedKP.BoundaryPrefixTable
import RootedKP.BoundaryPrefixBounds
import RootedKP.EndpointGrowth

/-! The finite endpoint certificates cover every starting vertex and directed
edge in all three INFINITE local charts. Transfer from actual halo graphs is
not part of this module. -/

namespace RootedKP.BoundaryCounts
open Honeycomb BoundaryCharts

theorem chart_prefix_bound (C : Chart) (k : ℕ) (hlo : 1 ≤ k) (hhi : k ≤ 10)
    (u forbidden : Vertex) (hf : forbidden ∈ next C u) :
    endpointCount C k u forbidden ≤ prefixCap k := by
  cases k with
  | zero => omega
  | succ n =>
    let i : Fin 10 := ⟨n, by omega⟩
    cases C with
    | bulk => rw [bulk_endpointCount_zero]; exact Nat.zero_le _
    | side => exact side_global_prefix_bound hhi (side_prefix_checks i) u forbidden hf
    | corner =>
      exact corner_global_prefix_bound hhi
        (side_prefix_checks i) (corner_prefix_checks i) u forbidden hf

/-- Uniform N(10)=64 upper bound at every directed edge of every local chart. -/
theorem chart_endpoint_ten (C : Chart) (u forbidden : Vertex)
    (hf : forbidden ∈ next C u) : endpointCount C 10 u forbidden ≤ 64 := by
  simpa only [prefixCap] using chart_prefix_bound C 10 (by decide) (by decide) u forbidden hf

/-- Verified N10 propagates to every longer endpoint walk in each local chart. -/
theorem chart_endpoint_long (C : Chart) (k : ℕ) (hk : 10 ≤ k)
    (u forbidden : Vertex) (hf : forbidden ∈ next C u) :
    endpointCount C k u forbidden ≤ 2 ^ (k - 4) :=
  endpointCount_le_from_ten C (chart_endpoint_ten C) k hk u forbidden hf

end RootedKP.BoundaryCounts
