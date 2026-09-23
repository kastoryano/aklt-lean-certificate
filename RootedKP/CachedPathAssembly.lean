import RootedKP.CachedPathEnumeration

namespace RootedKP.CachedPaths
open Honeycomb BoundaryCharts BoundaryCounts ShortRootCharts PackedSupports
open scoped BigOperators
set_option maxHeartbeats 0

def gatherStarts (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => gatherStarts n k ++
      (gather (upperStart k) n [upperStart k] ++ gather (leftStart k) n [leftStart k])

theorem hitCount_gatherStarts (r n k : ℕ) :
    hitCount r (gatherStarts n k) =
      (∑j∈Finset.range k,hitCount r (gather (upperStart j) n [upperStart j]))+
      (∑j∈Finset.range k,hitCount r (gather (leftStart j) n [leftStart j])) := by
  induction k with
  | zero => simp [gatherStarts,hitCount]
  | succ k ih =>
    simp only [gatherStarts,hitCount_append,ih,Finset.sum_range_succ]
    omega

theorem sum_starts62 (f : Vertex → ℕ) :
    (∑v∈starts 62,f v)=
      (∑k∈Finset.range 32,f (upperStart k))+(∑k∈Finset.range 32,f (leftStart k)) := by
  have hu : Function.Injective (fun k : ℕ => Vertex.a ((k : ℤ)-1) 1) := by
    intro a b h
    simp only [Vertex.a.injEq] at h
    omega
  have hl : Function.Injective (fun k : ℕ => Vertex.b (-2) (-(k : ℤ))) := by
    intro a b h
    simp only [Vertex.b.injEq] at h
    omega
  have hd : Disjoint
      ((Finset.range 32).image (fun k : ℕ => Vertex.a ((k : ℤ)-1) 1))
      ((Finset.range 32).image (fun k : ℕ => Vertex.b (-2) (-(k : ℤ)))) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hw
    cases he
  unfold starts
  change (∑v∈_,f v)=_
  rw [Finset.sum_union hd,Finset.sum_image (fun a _ b _ h => hu h),
    Finset.sum_image (fun a _ b _ h => hl h)]
  rfl

theorem catalogCount_eq_gatherStarts (root : List Vertex) (n : ℕ) :
    ShortRootRepresentatives.catalogCount root.toFinset n=
      hitCount (pack root) (gatherStarts n 32) := by
  rw [←cachedCatalogCount_eq,cachedCatalogCount,sum_starts62,hitCount_gatherStarts]

end RootedKP.CachedPaths
