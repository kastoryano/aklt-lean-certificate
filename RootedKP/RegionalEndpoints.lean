import RootedKP.RegionalChartCover
import RootedKP.BoundaryPrefixes

/-! Literal regional endpoint paths inject into a single verified local chart. -/
namespace RootedKP.RegionalEndpoints
open Honeycomb BoundaryCounts Enumeration LoopCounts
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

def next (F : Rectangle) (u : Vertex) : Finset Vertex :=
  (neighbors u).filter (fun v => Core F 200 u ∨ Core F 200 v)

@[simp] theorem mem_next (F : Rectangle) (u v : Vertex) :
    v ∈ next F u ↔ SunAdj F 200 u v := by simp [next, SunAdj]

def prefixes (F : Rectangle) : ℕ → Vertex → Vertex → Finset (List Vertex)
  | 0, u, _ => if Leaf F 200 u then {[u]} else ∅
  | n+1, u, forbidden => ((next F u).erase forbidden).biUnion (fun v =>
      (extensions (next F) n [v,u]).filter (endsAt (Leaf F 200)))

def count (F : Rectangle) : ℕ → Vertex → Vertex → ℕ
  | 0, u, _ => if Leaf F 200 u then 1 else 0
  | n+1, u, forbidden => ∑ v ∈ (next F u).erase forbidden,
      acceptedCount (next F) (endsAt (Leaf F 200)) n [v,u]

theorem count_eq_card (F : Rectangle) (n : ℕ) (u forbidden : Vertex) :
    count F n u forbidden = (prefixes F n u forbidden).card := by
  cases n with
  | zero => by_cases h : Leaf F 200 u <;> simp [count, prefixes, h]
  | succ n =>
    simp only [count, prefixes]
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro v _
      exact acceptedCount_eq_card _ _ _ _
    · intro v hv w hw hne
      apply Finset.disjoint_left.mpr
      intro result hr₁ hr₂
      have h₁ := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp hr₁).1
      have h₂ := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp hr₂).1
      have heq := (extends_drop h₁).symm.trans (extends_drop h₂)
      exact hne (List.cons.inj heq).1

lemma extends_contains {N : Vertex → Finset Vertex} {n : ℕ} {trail result : List Vertex}
    (h : Extends N n trail result) : ∀ v ∈ trail, v ∈ result := by
  induction h with
  | refl trail => exact fun _ hv => hv
  | @step u w us result n _ _ he ih =>
    intro v hv
    exact ih v (List.mem_cons_of_mem w hv)

lemma extends_within {F : Rectangle} {center : Vertex} {n R : ℕ} {trail result : List Vertex}
    (h : Extends (next F) n trail result)
    (ht : ∀ v ∈ trail, VertexWithin center v R) :
    ∀ v ∈ result, VertexWithin center v (R+n) := by
  induction h generalizing R with
  | refl trail => simpa using ht
  | @step u w us result n hw _ he ih =>
    have hu := ht u (List.mem_cons_self ..)
    have hnew := hu.trans (VertexWithin.of_adj ((mem_next F u w).mp hw).1)
    have htail : ∀ v ∈ w :: u :: us, VertexWithin center v (R+1) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hnew
      · exact (ht v hv).mono (Nat.le_succ R)
    have hh := ih htail
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma extends_map_chart {F : Rectangle} {center : Vertex} {R n : ℕ}
    (c : RegionalChartCover F center R) {trail result : List Vertex}
    (h : Extends (next F) n trail result)
    (hb : ∀ v ∈ result, VertexWithin center v R) :
    Extends (BoundaryCharts.next .corner) n (trail.map c.iso.vertex) (result.map c.iso.vertex) := by
  induction h with
  | refl trail => exact .refl _
  | @step u v us result n hv hnew he ih =>
    have hu : u ∈ result := extends_contains he u (by simp)
    apply Extends.step ((BoundaryCharts.mem_next _ _ _).mpr
      ((c.adjacency_iff (hb u hu) v).mp ((mem_next F u v).mp hv)))
    · intro hm
      change c.iso.vertex v ∈ (u :: us).map c.iso.vertex at hm
      obtain ⟨w,hw,heq⟩ := List.mem_map.mp hm
      exact hnew ((c.iso.vertex.injective heq) ▸ hw)
    · exact ih hb

/-- One common chart map injects the entire regional endpoint family; it is
chosen from the starting vertex and radius, not separately for each path. -/
theorem count_le_chart {F : Rectangle} {u forbidden : Vertex} {R n : ℕ}
    (c : RegionalChartCover F u R) (hn : n+1 ≤ R) :
    count F (n+1) u forbidden ≤
      endpointCount .corner (n+1) (c.iso.vertex u) (c.iso.vertex forbidden) := by
  rw [count_eq_card, endpointCount_eq_card]
  have hsub : (prefixes F (n+1) u forbidden).image (List.map c.iso.vertex) ⊆
      endpointPrefixes .corner (n+1) (c.iso.vertex u) (c.iso.vertex forbidden) := by
    intro result hm
    obtain ⟨trail,ht,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨v,hv,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨hvf,hvu⟩ := Finset.mem_erase.mp hv
    obtain ⟨he,hleaf⟩ := Finset.mem_filter.mp ht
    have he' := (mem_extensions_iff _ _ _ _).mp he
    have hstart : ∀ w ∈ [v,u], VertexWithin u w 1 := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact VertexWithin.of_adj ((mem_next F u _).mp hvu).1
      · have heq : w = u := List.mem_singleton.mp hw
        subst w
        exact VertexWithin.refl u 1
    have hbounded : ∀ w ∈ trail, VertexWithin u w R := by
      intro w hw
      exact (extends_within he' hstart w hw).mono (by omega)
    apply (mem_endpointPrefixes_iff _ _ _ _ _).mpr
    refine ⟨c.iso.vertex v, ?_, ?_, extends_map_chart c he' hbounded, ?_⟩
    · exact (c.adjacency_iff (VertexWithin.refl u R) v).mp ((mem_next F u v).mp hvu)
    · exact fun hh => hvf (c.iso.vertex.injective hh)
    · cases trail with
      | nil => exact False.elim hleaf
      | cons w ws =>
        exact (c.leaf_iff (hbounded w (List.mem_cons_self ..))).mp hleaf
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (List.map_injective_iff.mpr c.iso.vertex.injective)] at hc
  exact hc

/-- The literal regional N10 count is controlled by an infinite corner chart. -/
theorem regional_ten_le_chart (F : Rectangle) (u forbidden : Vertex)
    (hf : forbidden ∈ next F u) :
    ∃ c : RegionalChartCover F u 10,
      count F 10 u forbidden ≤ endpointCount .corner 10 (c.iso.vertex u) (c.iso.vertex forbidden) ∧
      c.iso.vertex forbidden ∈ BoundaryCharts.next .corner (c.iso.vertex u) := by
  obtain ⟨c⟩ := regional_chart_cover F u 10 ⟨forbidden,(mem_next F u forbidden).mp hf⟩ (by decide)
  refine ⟨c, count_le_chart c (by decide : 9+1 ≤ 10), ?_⟩
  exact (BoundaryCharts.mem_next _ _ _).mpr
    ((c.adjacency_iff (VertexWithin.refl u 10) forbidden).mp ((mem_next F u forbidden).mp hf))

end
end RootedKP.RegionalEndpoints
#print axioms RootedKP.RegionalEndpoints.count_le_chart
#print axioms RootedKP.RegionalEndpoints.regional_ten_le_chart
