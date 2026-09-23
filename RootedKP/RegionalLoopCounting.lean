import RootedKP.LoopEncoding
import RootedKP.ActivityBounds

namespace RootedKP.AKLT
open Honeycomb Enumeration LoopCounts
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def loopsOnEdge (F : Rectangle) (edge : Edge) (n : ℕ) : Finset (Polymer F) :=
  by classical exact Finset.univ.filter (fun p => p.kind = .loop ∧ edge ∈ p.edges ∧ p.length = n)

lemma loop_adj_of_edge {F : Rectangle} (p : Polymer F) (hk : p.kind = .loop)
    {u v : Vertex} (hm : s(u,v) ∈ p.edges) : Adj u v := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨q,hq⟩ := hr
  exact (simpleLoop_cyclic_adj q u v (by rwa [← loopEdges_eq_cyclicEdges, hq])).1

/-- Canonical edge sets inject into the verified single-orientation enumerator.
Neither reversing nor rotating a realization introduces any multiplicity. -/
theorem loopsOnEdge_card_le (F : Rectangle) (edge : Edge) (n : ℕ) :
    (loopsOnEdge F edge n).card ≤ (anchoredLoops n).card := by
  classical
  induction edge using Sym2.inductionOn with
  | hf u v =>
    let S := loopsOnEdge F s(u,v) n
    by_cases hempty : S = ∅
    · simpa [S, hempty]
    · obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hp' := Finset.mem_filter.mp hp
      obtain ⟨e,hu,hv,he⟩ := directed_edge_equiv (loop_adj_of_edge p hp'.2.1 hp'.2.2.1)
      have hex (p : {p // p ∈ S}) :
          ∃ r ∈ anchoredLoops n, cyclicEdges (r.map e) = p.val.edges := by
        have hm := (Finset.mem_filter.mp p.property).2
        obtain ⟨r,hr,hrec⟩ := polymer_loop_encoding e hu hv he p.val hm.1 hm.2.1
        exact ⟨r, by simpa [hm.2.2] using hr, hrec⟩
      let encode (p : {p // p ∈ S}) : {r // r ∈ anchoredLoops n} :=
        ⟨(hex p).choose, (hex p).choose_spec.1⟩
      have hi : Function.Injective encode := by
        intro p q hh
        apply Subtype.ext
        apply polymer_eq_of_loop_code p.val q.val
          (Finset.mem_filter.mp p.property).2.1 (Finset.mem_filter.mp q.property).2.1
        have hr := congrArg Subtype.val hh
        exact (hex p).choose_spec.2.symm.trans
          ((congrArg (fun r : List Vertex => cyclicEdges (r.map e)) hr).trans
            (hex q).choose_spec.2)
      simpa [S] using Fintype.card_le_of_injective encode hi

theorem Polymer.loop_length_ne_eight {F : Rectangle} (p : Polymer F)
    (hk : p.kind = .loop) : p.length ≠ 8 := by
  classical
  intro hl
  obtain ⟨edge,he⟩ := p.edges_nonempty
  have hm : p ∈ loopsOnEdge F edge 8 := by simp [loopsOnEdge, hk, he, hl]
  have hp := Finset.card_pos.mpr ⟨p,hm⟩
  have hb := loopsOnEdge_card_le F edge 8
  rw [loops8] at hb
  omega

theorem Polymer.loop_length_eq_six_or_ge_ten {F : Rectangle} (p : Polymer F)
    (hk : p.kind = .loop) : p.length = 6 ∨ 10 ≤ p.length := by
  have h6 := p.loop_length_ge_six hk
  have h2 := p.loop_length_even hk
  have h8 := p.loop_length_ne_eight hk
  omega

noncomputable def loopEdgeSet (F : Rectangle) (edge : Edge) : Finset (Polymer F) :=
  by classical exact Finset.univ.filter (fun p => p.kind = .loop ∧ edge ∈ p.edges)

def loopIndex {F : Rectangle} (p : Polymer F) : ℕ := (p.length - 6) / 2

lemma loop_length_index {F : Rectangle} (p : Polymer F) (hk : p.kind = .loop) :
    p.length = 6 + 2 * loopIndex p := by
  have h6 := p.loop_length_ge_six hk
  have h2 := p.loop_length_even hk
  unfold loopIndex
  omega

lemma loop_fiber_eq (F : Rectangle) (edge : Edge) (k : ℕ) :
    (loopEdgeSet F edge).filter (fun p => loopIndex p = k) =
      loopsOnEdge F edge (6 + 2 * k) := by
  classical
  ext p
  simp only [loopEdgeSet, loopsOnEdge, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hk,he⟩,hi⟩
    exact ⟨hk,he, by rw [loop_length_index p hk,hi]⟩
  · rintro ⟨hk,he,hl⟩
    refine ⟨⟨hk,he⟩, ?_⟩
    unfold loopIndex
    omega

lemma loop_length_fiber_mass_le (F : Rectangle) (edge : Edge) (k : ℕ) :
    (∑ p ∈ loopsOnEdge F edge (6 + 2 * k),
      (p.activity : ℝ) * Real.exp p.cost) ≤ anchoredEvenTerm k := by
  classical
  have hw : (0 : ℝ) ≤ (Arithmetic.weightCap (6 + 2 * k) : ℝ) := by
    exact_mod_cast Arithmetic.weightCap_nonneg (6 + 2 * k)
  calc
    _ ≤ ∑ _p ∈ loopsOnEdge F edge (6 + 2 * k),
        (Arithmetic.weightCap (6 + 2 * k) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := (Finset.mem_filter.mp hp).2.2.2
      simpa [hl] using polymer_budget_le_weightCap p
    _ = ((loopsOnEdge F edge (6 + 2 * k)).card : ℝ) *
        (Arithmetic.weightCap (6 + 2 * k) : ℝ) := by simp
    _ ≤ ((anchoredLoops (6 + 2 * k)).card : ℝ) *
        (Arithmetic.weightCap (6 + 2 * k) : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact_mod_cast loopsOnEdge_card_le F edge (6 + 2 * k)
    _ = _ := rfl

/-- The verified complete loop series bounds the actual regional loop mass
at every edge, uniformly in the rectangle and without a length cutoff. -/
theorem loop_edge_mass_le (F : Rectangle) (edge : Edge) :
    (∑ p ∈ loopEdgeSet F edge, (p.activity : ℝ) * Real.exp p.cost) ≤
      (Arithmetic.loopMass : ℝ) := by
  classical
  let indices := (loopEdgeSet F edge).image loopIndex
  have hf : ∀ p ∈ loopEdgeSet F edge, loopIndex p ∈ indices :=
    fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hf]
  calc
    _ ≤ ∑ k ∈ indices, anchoredEvenTerm k := by
      apply Finset.sum_le_sum
      intro k _
      rw [loop_fiber_eq]
      exact loop_length_fiber_mass_le F edge k
    _ ≤ ∑' k, anchoredEvenTerm k :=
      anchoredEvenTerm_summable.sum_le_tsum indices (fun k _ => anchoredEvenTerm_nonneg k)
    _ ≤ _ := anchoredEvenMass_le

end RootedKP.AKLT
#print axioms RootedKP.AKLT.loopsOnEdge_card_le
#print axioms RootedKP.AKLT.Polymer.loop_length_eq_six_or_ge_ten

#print axioms RootedKP.AKLT.loop_edge_mass_le
