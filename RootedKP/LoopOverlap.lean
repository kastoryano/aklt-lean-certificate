import RootedKP.PathConfinement
import RootedKP.CyclicEdges

/-! Literal loop overlaps can be charged to root edges with both endpoints
in the face core. In a path this omits at least the two outer leaf prongs. -/
namespace RootedKP.AKLT
open Honeycomb

lemma traversal_edge_at {vs : List Vertex} {i : ℕ} (hi : i + 1 < vs.length)
    (default : Vertex) : s(vs.getD i default, vs.getD (i + 1) default) ∈ traversalEdges vs := by
  induction vs generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases rest with
    | nil => simp at hi
    | cons b tail =>
      cases i with
      | zero => simp [traversalEdges]
      | succ i =>
        exact Finset.mem_insert_of_mem (by
          simpa using ih (by simpa using hi : i + 1 < (b :: tail).length))

lemma boundaryPath_edge_at {F : Rectangle} {R : ℕ} (p : BoundaryPath F R)
    {i : ℕ} (hi : i < p.length) : s(p.vertex i, p.vertex (i + 1)) ∈ pathEdges p := by
  exact traversal_edge_at (by have := p.vertices_length; omega) _

lemma boundaryPath_vertex_two_neighbors {F : Rectangle} {R : ℕ} (p : BoundaryPath F R)
    {v : Vertex} (hv : v ∈ p.vertices) (hc : Core F R v) :
    ∃ u w, u ≠ w ∧ s(v,u) ∈ pathEdges p ∧ s(v,w) ∈ pathEdges p := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hv
  have hvi : p.vertex i = v := by
    simp only [BoundaryPath.vertex, List.getD_eq_getElem _ _ hi, heq]
  have hin : i ≤ p.length := by have := p.vertices_length; omega
  have hlo : 0 < i := by
    by_contra hh
    have hz : i = 0 := by omega
    have hc' : Core F R (p.vertex i) := hvi.symm ▸ hc
    exact leaf_not_core p.start_leaf (by simpa [hz, p.at_start] using hc')
  have hhi : i < p.length := by
    by_contra hh
    have hz : i = p.length := by omega
    have hc' : Core F R (p.vertex i) := hvi.symm ▸ hc
    exact leaf_not_core p.finish_leaf (by simpa [hz, p.at_finish] using hc')
  have hp : i - 1 + 1 = i := by omega
  refine ⟨p.vertex (i - 1), p.vertex (i + 1), ?_, ?_, ?_⟩
  · intro h
    have := p.at_injective (i - 1) (by omega) (i + 1) (by omega) h
    omega
  · simpa [hp, hvi, Sym2.eq_swap] using boundaryPath_edge_at p (i := i - 1) (by omega)
  · simpa [hvi] using boundaryPath_edge_at p hhi

lemma cyclic_vertex_two_neighbors {vs : List Vertex} (hn : vs.Nodup) (hl : 3 ≤ vs.length)
    {v : Vertex} (hv : ∃ u, s(v,u) ∈ cyclicEdges vs) :
    ∃ u w, u ≠ w ∧ s(v,u) ∈ cyclicEdges vs ∧ s(v,w) ∈ cyclicEdges vs := by
  obtain ⟨u, hu⟩ := hv
  obtain ⟨rest, hlen, hedges, hnod⟩ := cyclic_edge_oriented (by omega) hu
  have hn' := hnod hn
  have hrest : rest ≠ [] := by intro h; simp [h] at hlen; omega
  obtain ⟨w, hw⟩ : ∃ w, rest.getLast? = some w := by
    cases hh : rest.getLast? with
    | none => exact False.elim (hrest (List.getLast?_eq_none_iff.mp hh))
    | some w => exact ⟨w, rfl⟩
  have hwm := List.mem_of_getLast? hw
  refine ⟨u, w, ?_, hu, ?_⟩
  · intro hh
    exact (List.nodup_cons.mp (List.nodup_cons.mp hn').2).1 (hh ▸ hwm)
  · have hw' : (v :: u :: rest).getLast? = some w := by
      cases rest with
      | nil => exact False.elim (hrest rfl)
      | cons z zs => simpa using hw
    rw [← hedges, cyclicEdges_eq rfl hw']
    simp [Sym2.eq_swap]

lemma three_neighbor_overlap {v a b c d : Vertex}
    (ha : Adj v a) (hb : Adj v b) (hc : Adj v c) (hd : Adj v d)
    (hab : a ≠ b) (hcd : c ≠ d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  classical
  by_contra h
  simp only [not_or] at h
  have hsub : ({a,b,c,d} : Finset Vertex) ⊆ neighbors v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (mem_neighbors _ _).mpr ha
    · exact (mem_neighbors _ _).mpr hb
    · exact (mem_neighbors _ _).mpr hc
    · exact (mem_neighbors _ _).mpr hd
  have hcard : ({a,b,c,d} : Finset Vertex).card = 4 := by simp_all
  have hh := Finset.card_le_card hsub
  rw [hcard, neighbors_card] at hh
  omega

namespace Polymer

variable {F : Rectangle}

lemma support_iff_incident (p : Polymer F) (v : Vertex) :
    v ∈ p.support ↔ ∃ u, s(v,u) ∈ p.edges := by
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    have hv' := Sym2.mem_toFinset.mp hve
    induction e using Sym2.inductionOn with
    | _ a b =>
      rcases Sym2.mem_iff.mp hv' with rfl | rfl
      · exact ⟨b, he⟩
      · exact ⟨a, by simpa [Sym2.eq_swap] using he⟩
  · rintro ⟨u, hu⟩
    exact Finset.mem_biUnion.mpr ⟨s(v,u), hu, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left v u)⟩

lemma edge_sunAdj (p : Polymer F) {u v : Vertex} (he : s(u,v) ∈ p.edges) :
    SunAdj F haloRadius u v := by
  have hr := p.realization
  cases hk : p.kind with
  | path =>
    rw [hk] at hr
    obtain ⟨r, h⟩ := hr
    rw [← h] at he
    exact traversalEdges_adj (fun _ _ => sunAdj_symm) r.consecutive u v he
  | loop =>
    rw [hk] at hr
    obtain ⟨r, h⟩ := hr
    rw [← h, loopEdges_eq_cyclicEdges] at he
    exact simpleLoop_cyclic_adj r u v he

lemma loop_two_neighbors (p : Polymer F) (hk : p.kind = .loop) {v : Vertex}
    (hv : v ∈ p.support) : ∃ u w, u ≠ w ∧ s(v,u) ∈ p.edges ∧ s(v,w) ∈ p.edges := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨r, h⟩ := hr
  have hi := (support_iff_incident p v).mp hv
  rw [← h, loopEdges_eq_cyclicEdges] at hi ⊢
  exact cyclic_vertex_two_neighbors r.nodup r.nondegenerate hi

lemma loop_vertex_core (p : Polymer F) (hk : p.kind = .loop) {v : Vertex}
    (hv : v ∈ p.support) : Core F haloRadius v := by
  obtain ⟨u, w, hne, hu, hw⟩ := loop_two_neighbors p hk hv
  classical
  by_contra hnc
  exact hne (noncore_core_neighbor_unique hnc
    ((p.edge_sunAdj hu).2.resolve_left hnc) ((p.edge_sunAdj hw).2.resolve_left hnc)
    (p.edge_sunAdj hu).1 (p.edge_sunAdj hw).1)

lemma core_vertex_two_neighbors (p : Polymer F) {v : Vertex}
    (hv : v ∈ p.support) (hc : Core F haloRadius v) :
    ∃ u w, u ≠ w ∧ s(v,u) ∈ p.edges ∧ s(v,w) ∈ p.edges := by
  cases hk : p.kind with
  | loop => exact loop_two_neighbors p hk hv
  | path =>
    have hr := p.realization
    rw [hk] at hr
    obtain ⟨r, h⟩ := hr
    obtain ⟨u, hu⟩ := (support_iff_incident p v).mp hv
    have hu' : s(v,u) ∈ traversalEdges r.vertices := by rw [← h] at hu; exact hu
    have hm : v ∈ r.vertices := vertex_mem_of_traversal_edge hu' (Sym2.mem_mk_left v u)
    rw [← h]
    exact boundaryPath_vertex_two_neighbors r hm hc

noncomputable def eligibleEdges (p : Polymer F) : Finset Edge := by
  classical
  exact p.edges.filter (fun e => ∀ v ∈ e, Core F haloRadius v)

lemma mem_eligibleEdges (p : Polymer F) (e : Edge) :
    e ∈ p.eligibleEdges ↔ e ∈ p.edges ∧ ∀ v ∈ e, Core F haloRadius v := by
  classical
  exact Finset.mem_filter

lemma eligibleEdges_subset (p : Polymer F) : p.eligibleEdges ⊆ p.edges := by
  classical
  exact Finset.filter_subset _ _

lemma eligibleEdges_card_loop (p : Polymer F) : p.eligibleEdges.card ≤ p.length :=
  Finset.card_le_card p.eligibleEdges_subset

lemma eligibleEdges_card_path (p : Polymer F) (hk : p.kind = .path) :
    p.eligibleEdges.card ≤ p.length - 2 := by
  classical
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨r, hr⟩ := hr
  have hlen := boundaryPath_length_ge_three r
  let e₀ : Edge := s(r.vertex 0, r.vertex 1)
  let e₁ : Edge := s(r.vertex (r.length - 1), r.vertex r.length)
  have he₀ : e₀ ∈ p.edges := by
    rw [← hr]
    exact boundaryPath_edge_at r (by omega)
  have he₁ : e₁ ∈ p.edges := by
    rw [← hr]
    simpa [e₁, Nat.sub_add_cancel (by omega : 1 ≤ r.length)] using
      boundaryPath_edge_at r (i := r.length - 1) (by omega)
  have hbad₀ : e₀ ∉ p.eligibleEdges := by
    intro h
    have hc := ((p.mem_eligibleEdges _).mp h).2 (r.vertex 0) (Sym2.mem_mk_left ..)
    exact leaf_not_core r.start_leaf (by simpa [r.at_start] using hc)
  have hbad₁ : e₁ ∉ p.eligibleEdges := by
    intro h
    have hc := ((p.mem_eligibleEdges _).mp h).2 (r.vertex r.length) (Sym2.mem_mk_right ..)
    exact leaf_not_core r.finish_leaf (by simpa [r.at_finish] using hc)
  have hne : e₀ ≠ e₁ := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨hh,_⟩ | ⟨hh,_⟩
    · have := r.at_injective 0 (by omega) (r.length - 1) (by omega) hh
      omega
    · have := r.at_injective 0 (by omega) r.length (by omega) hh
      omega
  have hsub : ({e₀,e₁} : Finset Edge) ⊆ p.edges \ p.eligibleEdges := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_sdiff.mpr ⟨he₀,hbad₀⟩
    · have heq : e = e₁ := Finset.mem_singleton.mp he
      subst e
      exact Finset.mem_sdiff.mpr ⟨he₁,hbad₁⟩
  have hc := Finset.card_le_card hsub
  have heq := Finset.card_sdiff_add_card_eq_card p.eligibleEdges_subset
  simp only [Finset.card_insert_of_notMem (by simpa using hne : e₀ ∉ ({e₁} : Finset Edge)),
    Finset.card_singleton] at hc
  unfold length
  omega

lemma incompatible_loop_shared_eligible_edge (p q : Polymer F) (hq : q.kind = .loop)
    (hinc : Incompatible p q) : ∃ e ∈ p.eligibleEdges, e ∈ q.edges := by
  classical
  obtain ⟨v, hvp, hvq⟩ := Finset.not_disjoint_iff.mp hinc
  have hc := q.loop_vertex_core hq hvq
  obtain ⟨a,b,hab,ha,hb⟩ := p.core_vertex_two_neighbors hvp hc
  obtain ⟨c,d,hcd,hc',hd⟩ := q.loop_two_neighbors hq hvq
  have hov := three_neighbor_overlap (p.edge_sunAdj ha).1 (p.edge_sunAdj hb).1
    (q.edge_sunAdj hc').1 (q.edge_sunAdj hd).1 hab hcd
  have make : ∀ u, s(v,u) ∈ p.edges → s(v,u) ∈ q.edges →
      ∃ e ∈ p.eligibleEdges, e ∈ q.edges := by
    intro u hp hu
    refine ⟨s(v,u), (p.mem_eligibleEdges _).mpr ⟨hp, ?_⟩, hu⟩
    intro w hw
    exact q.loop_vertex_core hq ((q.support_iff_incident w).mpr (by
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact ⟨u,hu⟩
      · exact ⟨v,by simpa [Sym2.eq_swap] using hu⟩))
  rcases hov with h | h | h | h
  · exact make a ha (by simpa [h] using hc')
  · exact make a ha (by simpa [h] using hd)
  · exact make b hb (by simpa [h] using hc')
  · exact make b hb (by simpa [h] using hd)

end Polymer
end RootedKP.AKLT
