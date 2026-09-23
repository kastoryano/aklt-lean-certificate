import RootedKP.LoopOverlap

namespace RootedKP.AKLT
open Honeycomb

lemma boundaryPath_noncore_vertex_endpoint {F : Rectangle} {R : ℕ}
    (p : BoundaryPath F R) {v : Vertex} (hv : v∈p.vertices) (hnc : ¬ Core F R v) :
    v=p.start ∨ v=p.finish := by
  obtain ⟨i,hi,hiv⟩ := List.mem_iff_getElem.mp hv
  have heq : p.vertex i=v := by simp only [BoundaryPath.vertex,List.getD_eq_getElem _ _ hi,hiv]
  have hin : i≤p.length := by have := p.vertices_length; omega
  by_cases hzero : i=0
  · left; simpa [hzero,p.at_start] using heq.symm
  by_cases hend : i=p.length
  · right; simpa [hend,p.at_finish] using heq.symm
  exact False.elim (hnc (heq ▸ IndexedConfinement.internal_core p.at_adjacent p.at_injective (by omega) (by omega)))

lemma edge_at_vertex {e : Edge} {v : Vertex} (hv : v∈e) : ∃u,e=s(v,u) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ⟨b,rfl⟩
    · exact ⟨a,Sym2.eq_swap⟩

namespace Polymer
variable {F : Rectangle}

/-- In the degree-three sun, any two intersecting polymers share an edge.
At a core both use two incident edges; at a leaf the edge is unique. -/
lemma incompatible_shared_edge (p q : Polymer F) (hinc : Incompatible p q) :
    ∃e∈p.edges,e∈q.edges := by
  classical
  obtain ⟨v,hvp,hvq⟩ := Finset.not_disjoint_iff.mp hinc
  by_cases hv : Core F haloRadius v
  · obtain ⟨a,b,hab,ha,hb⟩ := p.core_vertex_two_neighbors hvp hv
    obtain ⟨c,d,hcd,hc,hd⟩ := q.core_vertex_two_neighbors hvq hv
    rcases three_neighbor_overlap (p.edge_sunAdj ha).1 (p.edge_sunAdj hb).1
        (q.edge_sunAdj hc).1 (q.edge_sunAdj hd).1 hab hcd with h | h | h | h
    · exact ⟨s(v,a),ha,by simpa [h] using hc⟩
    · exact ⟨s(v,a),ha,by simpa [h] using hd⟩
    · exact ⟨s(v,b),hb,by simpa [h] using hc⟩
    · exact ⟨s(v,b),hb,by simpa [h] using hd⟩
  · obtain ⟨a,ha⟩ := (p.support_iff_incident v).mp hvp
    obtain ⟨b,hb⟩ := (q.support_iff_incident v).mp hvq
    have hp := p.edge_sunAdj ha
    have hq := q.edge_sunAdj hb
    have heq := noncore_core_neighbor_unique hv (hp.2.resolve_left hv) (hq.2.resolve_left hv) hp.1 hq.1
    exact ⟨s(v,a),ha,by simpa [heq] using hb⟩

lemma noneligibleEdges_card_loop (p : Polymer F) (hk : p.kind=.loop) :
    (p.edges \ p.eligibleEdges).card=0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hep,hne⟩ := Finset.mem_sdiff.mp he
  apply hne
  apply (p.mem_eligibleEdges e).mpr
  refine ⟨hep,?_⟩
  intro v hv
  apply p.loop_vertex_core hk
  exact Finset.mem_biUnion.mpr ⟨e,hep,Sym2.mem_toFinset.mpr hv⟩

/-- A path has at most two noneligible edges: its two actual leaf prongs. -/
lemma noneligibleEdges_card_path (p : Polymer F) (hk : p.kind=.path) :
    (p.edges \ p.eligibleEdges).card≤2 := by
  classical
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨r,hr⟩ := hr
  have hlen := boundaryPath_length_ge_three r
  let e₀ : Edge := s(r.start,r.vertex 1)
  let e₁ : Edge := s(r.finish,r.vertex (r.length-1))
  have hsub : p.edges \ p.eligibleEdges ⊆ {e₀,e₁} := by
    intro e he
    obtain ⟨hep,hne⟩ := Finset.mem_sdiff.mp he
    have hbad : ¬∀v∈e,Core F haloRadius v := by
      intro hh
      exact hne ((p.mem_eligibleEdges e).mpr ⟨hep,hh⟩)
    push_neg at hbad
    obtain ⟨v,hve,hv⟩ := hbad
    obtain ⟨u,rfl⟩ := edge_at_vertex hve
    have hvm : v∈r.vertices := vertex_mem_of_traversal_edge (by rw [← hr] at hep; exact hep) (Sym2.mem_mk_left v u)
    rcases boundaryPath_noncore_vertex_endpoint r hvm hv with h | h
    · subst v
      have hprong : SunAdj F haloRadius r.start (r.vertex 1) := by
        simpa [r.at_start] using r.at_adjacent 0 (by omega)
      obtain ⟨a,ha,hunique⟩ := r.start_leaf
      have hu : u=r.vertex 1 := (hunique _ (p.edge_sunAdj hep)).trans (hunique _ hprong).symm
      simp [e₀,hu]
    · subst v
      have heq : r.length-1+1=r.length := by omega
      have hprong : SunAdj F haloRadius r.finish (r.vertex (r.length-1)) := by
        simpa [heq,r.at_finish] using sunAdj_symm (r.at_adjacent (r.length-1) (by omega))
      obtain ⟨a,ha,hunique⟩ := r.finish_leaf
      have hu : u=r.vertex (r.length-1) := (hunique _ (p.edge_sunAdj hep)).trans (hunique _ hprong).symm
      simp [e₁,hu]
  have hh := Finset.card_le_card hsub
  have hpair : ({e₀,e₁} : Finset Edge).card≤2 := by by_cases hh : e₀=e₁ <;> simp [hh]
  omega

end Polymer
end RootedKP.AKLT
