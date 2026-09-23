import RootedKP.BoundaryFastCounts

/-!
# Exact endpoint-prefix enumeration

`endpointCount C k u forbidden` counts simple k-edge paths from u to a chart
leaf whose first edge is not u--forbidden. This is the reverse orientation of
the C++ `dfsn` count. No maximum over starting vertices or numerical envelope
is asserted by this module.
-/

namespace RootedKP.BoundaryCounts

open Honeycomb BoundaryCharts Enumeration LoopCounts
open scoped BigOperators

def endpointPrefixes (C : Chart) : ℕ → Vertex → Vertex → Finset (List Vertex)
  | 0, u, _ => if Leaf C u then {[u]} else ∅
  | n + 1, u, forbidden =>
    ((next C u).erase forbidden).biUnion (fun v =>
      (extensions (next C) n [v, u]).filter (endsAt (Leaf C)))

/-- Independent simple-step specification, with only the FIRST edge excluded. -/
def EndpointTraversal (C : Chart) (n : ℕ) (u forbidden : Vertex)
    (trail : List Vertex) : Prop :=
  ∃ v, BoundaryCharts.Adj C u v ∧ v ≠ forbidden ∧
    Extends (next C) n [v, u] trail ∧ endsAt (Leaf C) trail

theorem mem_endpointPrefixes_iff (C : Chart) (n : ℕ) (u forbidden : Vertex)
    (trail : List Vertex) :
    trail ∈ endpointPrefixes C (n + 1) u forbidden ↔
      EndpointTraversal C n u forbidden trail := by
  simp only [endpointPrefixes, EndpointTraversal, Finset.mem_biUnion,
    Finset.mem_erase, Finset.mem_filter, mem_extensions_iff, mem_next]
  constructor
  · rintro ⟨v, ⟨hv, hadj⟩, he, hend⟩
    exact ⟨v, hadj, hv, he, hend⟩
  · rintro ⟨v, hadj, hv, he, hend⟩
    exact ⟨v, ⟨hv, hadj⟩, he, hend⟩

theorem endpointPrefixes_simple {C : Chart} {n : ℕ} {u forbidden : Vertex}
    {trail : List Vertex} (h : trail ∈ endpointPrefixes C (n + 1) u forbidden) :
    trail.Nodup ∧ trail.length = n + 2 := by
  obtain ⟨v, hadj, _, he, _⟩ := (mem_endpointPrefixes_iff _ _ _ _ _).mp h
  have hne : v ≠ u := by
    rintro rfl
    exact Honeycomb.adj_irrefl _ hadj.1
  refine ⟨he.nodup (by simp [hne]), ?_⟩
  have hl := he.length
  simp only [List.length_cons, List.length_nil] at hl
  omega

def endpointCount (C : Chart) : ℕ → Vertex → Vertex → ℕ
  | 0, u, _ => if Leaf C u then 1 else 0
  | n + 1, u, forbidden =>
    ∑ v ∈ (next C u).erase forbidden,
      acceptedCount (next C) (endsAt (Leaf C)) n [v, u]

/-- The direct counter is exactly the size of the complete traversal set. -/
theorem endpointCount_eq_card (C : Chart) (n : ℕ) (u forbidden : Vertex) :
    endpointCount C n u forbidden = (endpointPrefixes C n u forbidden).card := by
  cases n with
  | zero =>
    by_cases h : Leaf C u <;> simp [endpointCount, endpointPrefixes, h]
  | succ n =>
    simp only [endpointCount, endpointPrefixes]
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro v _
      exact acceptedCount_eq_card _ _ _ _
    · intro v hv w hw hne
      apply Finset.disjoint_left.mpr
      intro trail hv' hw'
      have he₁ := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp hv').1
      have he₂ := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp hw').1
      have heq := (extends_drop he₁).symm.trans (extends_drop he₂)
      exact hne (List.cons.inj heq).1

/-- All-size elementary envelope after the first edge, valid for every chart. -/
theorem endpointCount_le_binary (C : Chart) (n : ℕ) (u forbidden : Vertex)
    (hforbidden : forbidden ∈ next C u) :
    endpointCount C (n + 1) u forbidden ≤ 2 ^ (n + 1) := by
  have hdegree : ∀ v, (next C v).card ≤ 3 := by
    intro v
    exact (Finset.card_filter_le _ _).trans_eq (neighbors_card v)
  have hchoices : ((next C u).erase forbidden).card ≤ 2 := by
    have h := hdegree u
    rw [Finset.card_erase_of_mem hforbidden]
    omega
  calc
    endpointCount C (n + 1) u forbidden ≤
        ∑ _v ∈ (next C u).erase forbidden, 2 ^ n := by
      apply Finset.sum_le_sum
      intro v hv
      rw [acceptedCount_eq_card]
      apply (Finset.card_filter_le _ _).trans
      apply card_extensions_after_edge_le (next C)
        (fun x y h => (mem_next C y x).mpr (BoundaryCharts.adj_symm ((mem_next C x y).mp h)))
        hdegree n v u []
      exact (mem_next C v u).mpr (BoundaryCharts.adj_symm
        ((mem_next C u v).mp (Finset.mem_erase.mp hv).2))
    _ = ((next C u).erase forbidden).card * 2 ^ n := by simp
    _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ hchoices
    _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

end RootedKP.BoundaryCounts
