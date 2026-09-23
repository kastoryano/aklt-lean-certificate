import RootedKP.ShortRootPruned
namespace RootedKP.ShortRootCharts
open Honeycomb BoundaryCharts Enumeration LoopCounts BoundaryCounts

def upperRootCount (root : Finset Vertex) (n k : ℕ) : ℕ :=
  let start := Vertex.a ((k : ℤ)-1) 1
  BoundaryCounts.prunedCount .corner (accepts root start) (endpointPossible .corner) n [start]

def leftRootCount (root : Finset Vertex) (n k : ℕ) : ℕ :=
  let start := Vertex.b (-2) (-(k : ℤ))
  BoundaryCounts.prunedCount .corner (accepts root start) (endpointPossible .corner) n [start]

/-- Splitting by starting leaf lets each kernel computation be cached as a
small certificate. The final sum still counts the same complete search. -/
theorem prunedRootCount_eq_sums (root : Finset Vertex) (n : ℕ) :
    prunedRootCount root n =
      (∑ k ∈ Finset.range ((n+1)/2+1), upperRootCount root n k) +
      (∑ k ∈ Finset.range ((n+1)/2+1), leftRootCount root n k) := by
  have hu : Function.Injective (fun (k : ℕ) => Vertex.a ((k : ℤ)-1) 1) := by
    intro a b h
    simp only [Vertex.a.injEq] at h
    omega
  have hl : Function.Injective (fun (k : ℕ) => Vertex.b (-2) (-(k : ℤ))) := by
    intro a b h
    simp only [Vertex.b.injEq] at h
    omega
  have hd : Disjoint
      ((Finset.range ((n+1)/2+1)).image (fun (k : ℕ) => Vertex.a ((k : ℤ)-1) 1))
      ((Finset.range ((n+1)/2+1)).image (fun (k : ℕ) => Vertex.b (-2) (-(k : ℤ)))) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hw
    cases he
  unfold prunedRootCount starts
  rw [Finset.sum_union hd,Finset.sum_image (fun a _ b _ h => hu h),
    Finset.sum_image (fun a _ b _ h => hl h)]
  rfl

end RootedKP.ShortRootCharts
