import RootedKP.PolymerRingCover
namespace RootedKP.AKLT
open Honeycomb
open scoped Classical
namespace Polymer
variable {F : Rectangle}
def traceLength (p : Polymer F) : ℕ := if p.kind=.path then p.length-2 else p.length
lemma core_trace_trimmed (p : Polymer F) :
    ∃u v n S,TracedWalk Adj u v n S ∧ n≤p.traceLength ∧
      (∀w∈S,Core F haloRadius w) ∧
      ∀w∈p.support,Core F haloRadius w→w∈S := by
  have hr := p.realization
  cases hk : p.kind with
  | path =>
    simp only [traceLength,hk,ite_true]
    rw [hk] at hr
    obtain ⟨r,hr⟩ := hr
    have hn := boundaryPath_length_ge_three r
    have hplen := p.length_of_path_realization r hr
    have hsupport : p.support=r.vertices.toFinset := by
      rw [support,←hr,path_support_eq]
    obtain ⟨S,hS,hmem⟩ := traced_index_segment (fun k hk => (r.at_adjacent k hk).1)
      1 (r.length-2) (by omega)
    refine ⟨r.vertex 1,r.vertex (1+(r.length-2)),r.length-2,S,hS,by omega,?_,?_⟩
    · intro w hw
      obtain ⟨j,hj,rfl⟩ := (hmem w).mp hw
      exact IndexedConfinement.internal_core r.at_adjacent r.at_injective (by omega) (by omega)
    · intro w hw hc
      rw [hsupport,List.mem_toFinset] at hw
      obtain ⟨i,hi,hw⟩ := List.mem_iff_getElem.mp hw
      have heq : r.vertex i=w := by simp only [BoundaryPath.vertex,List.getD_eq_getElem _ _ hi,hw]
      have hin : i≤r.length := by have := r.vertices_length; omega
      have hlo : 0 < i := by
        by_contra hh
        have hz : i=0 := by omega
        have hc' : Core F haloRadius (r.vertex i) := heq.symm ▸ hc
        exact Honeycomb.leaf_not_core r.start_leaf (by simpa [hz,r.at_start] using hc')
      have hhi : i < r.length := by
        by_contra hh
        have hz : i=r.length := by omega
        have hc' : Core F haloRadius (r.vertex i) := heq.symm ▸ hc
        exact Honeycomb.leaf_not_core r.finish_leaf (by simpa [hz,r.at_finish] using hc')
      apply (hmem w).mpr
      refine ⟨i-1,by omega,?_⟩
      have hi' : 1+(i-1)=i := by omega
      simpa only [hi'] using heq.symm
  | loop =>
    simpa only [traceLength,hk,show Kind.loop≠Kind.path by decide,ite_false] using p.core_trace

theorem ring_cover_trimmed (p : Polymer F) {d K : ℕ} (hd : d≤4) (hK : K≤86) :
    ∃ parts : List (TracePiece (Ring F d)),
      (parts.map TracePiece.length).sum + K*parts.length ≤ p.traceLength+K ∧
      ∀q:Polymer F, Incompatible p q →
        (∀w∈q.support,¬Core F (200-(d+1)) w) →
        ∃piece∈parts,¬Disjoint piece.support q.support := by
  obtain ⟨u,v,n,S,htrace,hn,hcore,hcontains⟩ := p.core_trace_trimmed
  obtain ⟨parts,hbudget,hcover⟩ := core_trace_ring_cover hd hK htrace hcore
  refine ⟨parts,by omega,?_⟩
  intro q hinc hconf
  obtain ⟨w,hwp,hwq,hwcore⟩ := p.incompatible_core_contact q hinc
  obtain ⟨piece,hpiece,hw⟩ := hcover w (hcontains w hwp hwcore) ⟨hwcore,hconf w hwq⟩
  exact ⟨piece,hpiece,Finset.not_disjoint_iff.mpr ⟨w,hw,hwq⟩⟩


end Polymer
end RootedKP.AKLT
