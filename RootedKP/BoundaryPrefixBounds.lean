import RootedKP.BoundaryPrefixCertificates
import RootedKP.BoundarySideBound

namespace RootedKP.BoundaryCounts
open Honeycomb BoundaryCharts Enumeration LoopCounts

set_option maxHeartbeats 0

/-- Transport endpoint walks by an injective chart graph map. -/
theorem endpointCount_le_of_map {C D : Chart} (f : Vertex → Vertex)
    (hinj : Function.Injective f)
    (hstep : ∀ u v, BoundaryCharts.Adj C u v → BoundaryCharts.Adj D (f u) (f v))
    (n : ℕ) (u forbidden : Vertex)
    (hend : ∀ trail, EndpointTraversal C n u forbidden trail →
      endsAt (Leaf D) (trail.map f)) :
    endpointCount C (n + 1) u forbidden ≤ endpointCount D (n + 1) (f u) (f forbidden) := by
  rw [endpointCount_eq_card, endpointCount_eq_card]
  have hsub : (endpointPrefixes C (n + 1) u forbidden).image (List.map f) ⊆
      endpointPrefixes D (n + 1) (f u) (f forbidden) := by
    intro result hm
    obtain ⟨trail, ht, rfl⟩ := Finset.mem_image.mp hm
    have hh := (mem_endpointPrefixes_iff _ _ _ _ _).mp ht
    have hhend := hend trail hh
    obtain ⟨v, hv, hne, he, _⟩ := hh
    apply (mem_endpointPrefixes_iff _ _ _ _ _).mpr
    exact ⟨f v, hstep _ _ hv, fun h => hne (hinj h),
      extends_map f hinj hstep he, hhend⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (List.map_injective_iff.mpr hinj)] at hc
  exact hc

theorem endpointTraversal_extends {C : Chart} {n : ℕ} {u forbidden : Vertex}
    {trail : List Vertex} (h : EndpointTraversal C n u forbidden trail) :
    Extends (next C) (n + 1) [u] trail := by
  obtain ⟨v, hadj, _, he, _⟩ := h
  apply Extends.step ((mem_next C u v).mpr hadj) _ he
  simp only [List.mem_singleton]
  rintro rfl
  exact Honeycomb.adj_irrefl _ hadj.1

def qCoord : Vertex → ℤ | .a q _ | .b q _ => q
def rCoord : Vertex → ℤ | .a _ r | .b _ r => r

theorem exists_phase (u : Vertex) : ∃ t, phaseVertex t (qCoord u) (rCoord u) = u := by
  cases u with
  | a q r => exact ⟨0, rfl⟩
  | b q r => exact ⟨1, rfl⟩

theorem exists_neighborAt {u v : Vertex} (h : Honeycomb.Adj u v) :
    ∃ i, neighborAt u i = v := by
  cases u with
  | a q r =>
    cases v with
    | a q' r' => exact False.elim h
    | b q' r' =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  | b q r =>
    cases v with
    | b q' r' => exact False.elim h
    | a q' r' =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · refine ⟨1, ?_⟩; simp [neighborAt]
      · refine ⟨2, ?_⟩; simp [neighborAt]

theorem side_check_applies {n : ℕ} (hcheck : SidePrefixCheck n) {u f : Vertex}
    (hr : rCoord u = 0) (hq : -4 ≤ qCoord u ∧ qCoord u ≤ 1)
    (hf : f ∈ next .side u) : endpointCount .side n u f ≤ prefixCap n := by
  obtain ⟨t, ht⟩ := exists_phase u
  obtain ⟨i, hi⟩ := exists_neighborAt ((mem_next _ _ _).mp hf).1
  let q : Fin 6 := ⟨(qCoord u + 4).toNat, by omega⟩
  have hqval : (q.val : ℤ) - 4 = qCoord u := by dsimp [q]; omega
  have hu : phaseVertex t ((q.val : ℤ) - 4) 0 = u := by rw [hqval, ← hr]; exact ht
  have hh := hcheck t q i
  dsimp only at hh
  rw [hu, hi, endpointFastCount_eq] at hh
  exact hh ((mem_next _ _ _).mp hf).2

theorem corner_check_applies {n : ℕ} (hcheck : CornerPrefixCheck n) {u f : Vertex}
    (hq : -2 ≤ qCoord u ∧ qCoord u ≤ 3)
    (hr : -4 ≤ rCoord u ∧ rCoord u ≤ 1)
    (hf : f ∈ next .corner u) : endpointCount .corner n u f ≤ prefixCap n := by
  obtain ⟨t, ht⟩ := exists_phase u
  obtain ⟨i, hi⟩ := exists_neighborAt ((mem_next _ _ _).mp hf).1
  let q : Fin 6 := ⟨(qCoord u + 2).toNat, by omega⟩
  let r : Fin 6 := ⟨(rCoord u + 4).toNat, by omega⟩
  have hqval : (q.val : ℤ) - 2 = qCoord u := by dsimp [q]; omega
  have hrval : (r.val : ℤ) - 4 = rCoord u := by dsimp [r]; omega
  have hu : phaseVertex t ((q.val : ℤ) - 2) ((r.val : ℤ) - 4) = u := by
    rw [hqval, hrval]; exact ht
  have hh := hcheck t q r i
  dsimp only at hh
  rw [hu, hi, endpointFastCount_eq] at hh
  exact hh ((mem_next _ _ _).mp hf).2

def shiftR (s : ℤ) : Vertex → Vertex
  | .a q r => .a q (r + s)
  | .b q r => .b q (r + s)

theorem shiftR_injective (s : ℤ) : Function.Injective (shiftR s) := by
  intro u v h
  cases u <;> cases v <;> simp_all [shiftR]

theorem shiftR_side_adj (s : ℤ) {u v : Vertex} (h : BoundaryCharts.Adj .side u v) :
    BoundaryCharts.Adj .side (shiftR s u) (shiftR s v) := by
  cases u <;> cases v <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, shiftR] <;> omega

theorem side_global_prefix_bound {n : ℕ} (hn : n + 1 ≤ 10)
    (hcheck : SidePrefixCheck (n + 1)) (u f : Vertex) (hf : f ∈ next .side u) :
    endpointCount .side (n + 1) u f ≤ prefixCap (n + 1) := by
  have hadj := (mem_next .side u f).mp hf
  have hqu : qCoord u ≤ 1 := by
    cases u <;> cases f <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, qCoord] <;> omega
  by_cases hlo : -4 ≤ qCoord u
  · let g := shiftR (-rCoord u)
    apply (endpointCount_le_of_map g (shiftR_injective _) (fun _ _ => shiftR_side_adj _)
      n u f ?_).trans
    · apply side_check_applies hcheck
      · cases u <;> simp [g, shiftR, rCoord]
      · cases u <;> simpa [g, shiftR, qCoord] using And.intro hlo hqu
      · exact (mem_next _ _ _).mpr (shiftR_side_adj _ hadj)
    · intro trail ht
      obtain ⟨v, _, _, _, hend⟩ := ht
      cases trail with
      | nil => exact False.elim hend
      | cons w ws =>
        have hw := (leafCode_iff .side w).mpr hend
        apply (leafCode_iff .side (g w)).mp
        cases w <;> simpa [g, shiftR, leafCode] using hw
  · have hz : endpointCount .side (n + 1) u f = 0 := by
      rw [endpointCount_eq_card, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro trail ht
      have he := (mem_endpointPrefixes_iff _ _ _ _ _).mp ht
      have hext := endpointTraversal_extends he
      obtain ⟨v, _, _, _, hend⟩ := he
      cases trail with
      | nil => exact False.elim hend
      | cons w ws =>
        have hw := (leafCode_iff .side w).mpr hend
        have hb := extension_height_bounds .side heightQ heightQ_lipschitz
          hext u [] w ws rfl rfl
        cases u <;> cases w <;> simp_all [leafCode, qCoord, heightQ] <;> omega
    rw [hz]
    exact Nat.zero_le _

/-- Uniform corner bound: outside the finite box, one leaf ray is unreachable
in ten steps and the remaining ray injects into the straight-side chart. -/
theorem corner_global_prefix_bound {n : ℕ} (hn : n + 1 ≤ 10)
    (hside : SidePrefixCheck (n + 1)) (hcorner : CornerPrefixCheck (n + 1))
    (u f : Vertex) (hf : f ∈ next .corner u) :
    endpointCount .corner (n + 1) u f ≤ prefixCap (n + 1) := by
  have hadj := (mem_next .corner u f).mp hf
  have hqlo : -2 ≤ qCoord u := by
    cases u <;> cases f <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, qCoord] <;> omega
  have hrhi : rCoord u ≤ 1 := by
    cases u <;> cases f <;> simp_all [BoundaryCharts.Adj, Honeycomb.Adj, core, rCoord] <;> omega
  by_cases hqhi : qCoord u ≤ 3
  · by_cases hrlo : -4 ≤ rCoord u
    · exact corner_check_applies hcorner ⟨hqlo, hqhi⟩ ⟨hrlo, hrhi⟩ hf
    · apply (endpointCount_le_of_map (leftToSide 0) (leftToSide_injective 0)
        (fun _ _ => leftToSide_adj 0) n u f ?_).trans
      · exact side_global_prefix_bound hn hside _ _
          ((mem_next _ _ _).mpr (leftToSide_adj 0 hadj))
      · intro trail ht
        have hext := endpointTraversal_extends ht
        obtain ⟨v, _, _, _, hend⟩ := ht
        cases trail with
        | nil => exact False.elim hend
        | cons w ws =>
          have hw := (leafCode_iff .corner w).mpr hend
          change upperLeaf w ∨ leftLeaf w at hw
          rcases hw with hu | hl
          · have hb := extension_height_bounds .corner heightR heightR_lipschitz
              hext u [] w ws rfl rfl
            cases u <;> cases w <;> simp_all [upperLeaf, rCoord, heightR] <;> omega
          · apply (leafCode_iff .side (leftToSide 0 w)).mp
            cases w <;> simp_all [leftLeaf, leftToSide, leafCode]
  · apply (endpointCount_le_of_map (upperToSide 0) (upperToSide_injective 0)
      (fun _ _ => upperToSide_adj 0) n u f ?_).trans
    · exact side_global_prefix_bound hn hside _ _
        ((mem_next _ _ _).mpr (upperToSide_adj 0 hadj))
    · intro trail ht
      have hext := endpointTraversal_extends ht
      obtain ⟨v, _, _, _, hend⟩ := ht
      cases trail with
      | nil => exact False.elim hend
      | cons w ws =>
        have hw := (leafCode_iff .corner w).mpr hend
        change upperLeaf w ∨ leftLeaf w at hw
        rcases hw with hu | hl
        · apply (leafCode_iff .side (upperToSide 0 w)).mp
          cases w <;> simp_all [upperLeaf, upperToSide, leafCode]
        · have hb := extension_height_bounds .corner heightQ heightQ_lipschitz
            hext u [] w ws rfl rfl
          cases u <;> cases w <;> simp_all [leftLeaf, qCoord, heightQ] <;> omega

theorem bulk_endpointCount_zero (n : ℕ) (u f : Vertex) : endpointCount .bulk (n + 1) u f = 0 := by
  rw [endpointCount_eq_card, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro trail ht
  obtain ⟨v, _, _, _, hend⟩ := (mem_endpointPrefixes_iff _ _ _ _ _).mp ht
  cases trail with
  | nil => exact False.elim hend
  | cons w ws => exact (leafCode_iff .bulk w).mpr hend

end RootedKP.BoundaryCounts
