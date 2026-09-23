import RootedKP.RootExcursions
import RootedKP.PathOverlap

namespace RootedKP.AKLT
open Honeycomb

lemma traversal_support_eq {vs : List Vertex} (hlen : 2≤vs.length) :
    (traversalEdges vs).biUnion Sym2.toFinset = vs.toFinset := by
  induction vs with
  | nil => simp at hlen
  | cons u rest ih =>
    cases rest with
    | nil => simp at hlen
    | cons v rest =>
      cases rest with
      | nil => simp [traversalEdges,Sym2.toFinset_mk_eq]
      | cons w rest =>
        have ht := ih (by simp : 2≤(v::w::rest).length)
        rw [traversalEdges,Finset.biUnion_insert,Sym2.toFinset_mk_eq,ht]
        simp [Finset.insert_comm]

lemma path_support_eq {F : Rectangle} {R : ℕ} (r : BoundaryPath F R) :
    (pathEdges r).biUnion Sym2.toFinset=r.vertices.toFinset := by
  apply traversal_support_eq
  have := boundaryPath_length_ge_three r
  unfold BoundaryPath.length at this
  omega

lemma loop_support_eq {F : Rectangle} {R : ℕ} (r : SimpleLoop F R) :
    (loopEdges r).biUnion Sym2.toFinset=r.vertices.toFinset := by
  have hs : r.start∈r.vertices := List.mem_of_head? r.head_eq
  have hf : r.finish∈r.vertices := List.mem_of_getLast? r.last_eq
  have ht := traversal_support_eq (by have := r.nondegenerate; omega : 2≤r.vertices.length)
  simp only [loopEdges,Finset.biUnion_insert,Sym2.toFinset_mk_eq,ht]
  simp [hs,hf]

lemma listWalk_adj_of_sun {F : Rectangle} {R : ℕ} {vs : List Vertex}
    (h : ListWalk (SunAdj F R) vs) : ListWalk Adj vs := by
  induction vs with
  | nil => trivial
  | cons a rest ih =>
    cases rest with
    | nil => trivial
    | cons b rest => exact ⟨h.1.1,ih h.2⟩

lemma traced_of_list {E : Vertex→Vertex→Prop} {vs : List Vertex} {u v : Vertex}
    (hh : vs.head?=some u) (hl : vs.getLast?=some v) (hw : ListWalk E vs) :
    TracedWalk E u v (vs.length-1) vs.toFinset := by
  induction vs generalizing u with
  | nil => simp at hh
  | cons a rest ih =>
    have ha : a=u := by simpa using hh
    subst u
    cases rest with
    | nil =>
      have hv : a=v := by simpa using hl
      subst v
      simpa using TracedWalk.nil (E:=E) a
    | cons b rest =>
      have ht := ih rfl (by simpa using hl) hw.2
      simpa using TracedWalk.cons hw.1 ht

lemma traced_index_segment {v : ℕ→Vertex} {n : ℕ}
    (he : ∀i,i<n→Adj (v i) (v (i+1))) (i k : ℕ) (hik : i+k≤n) :
    ∃S,TracedWalk Adj (v i) (v (i+k)) k S ∧
      ∀w,w∈S↔∃j,j≤k∧w=v (i+j) := by
  induction k generalizing i with
  | zero => exact ⟨{v i},by simpa using TracedWalk.nil (v i),by simp⟩
  | succ k ih =>
    obtain ⟨S,hS,hmem⟩ := ih (i+1) (by omega)
    refine ⟨insert (v i) S,?_,?_⟩
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        TracedWalk.cons (he i (by omega)) hS
    · intro w
      constructor
      · intro hw
        rcases Finset.mem_insert.mp hw with hw | hw
        · exact ⟨0,by omega,by simpa using hw⟩
        · obtain ⟨j,hj,hw⟩ := (hmem w).mp hw
          exact ⟨j+1,by omega,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw⟩
      · rintro ⟨j,hj,hw⟩
        by_cases hz : j=0
        · exact Finset.mem_insert.mpr (Or.inl (by simpa [hz] using hw))
        · apply Finset.mem_insert_of_mem
          apply (hmem w).mpr
          refine ⟨j-1,by omega,?_⟩
          have hi' : i+1+(j-1)=i+j := by omega
          simpa only [hi'] using hw

namespace Polymer
variable {F : Rectangle}

lemma incompatible_core_contact (p q : Polymer F) (hinc : Incompatible p q) :
    ∃v,v∈p.support∧v∈q.support∧Core F haloRadius v := by
  obtain ⟨e,hep,heq⟩ := p.incompatible_shared_edge q hinc
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hc := (p.edge_sunAdj hep).2
    have memp : ∀w∈s(u,v),w∈p.support := fun w hw =>
      Finset.mem_biUnion.mpr ⟨s(u,v),hep,Sym2.mem_toFinset.mpr hw⟩
    have memq : ∀w∈s(u,v),w∈q.support := fun w hw =>
      Finset.mem_biUnion.mpr ⟨s(u,v),heq,Sym2.mem_toFinset.mpr hw⟩
    rcases hc with hc | hc
    · exact ⟨u,memp u (Sym2.mem_mk_left u v),memq u (Sym2.mem_mk_left u v),hc⟩
    · exact ⟨v,memp v (Sym2.mem_mk_right u v),memq v (Sym2.mem_mk_right u v),hc⟩

/-- Every polymer admits an actual outer-core trace of length at most its
canonical edge length covering all its core vertices. Path roots are
trimmed by exactly their two outer leaf prongs; loop roots retain all edges. -/
lemma core_trace (p : Polymer F) :
    ∃u v n S,TracedWalk Adj u v n S ∧ n≤p.length ∧
      (∀w∈S,Core F haloRadius w) ∧
      ∀w∈p.support,Core F haloRadius w→w∈S := by
  have hr := p.realization
  cases hk : p.kind with
  | path =>
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
    rw [hk] at hr
    obtain ⟨r,hr⟩ := hr
    have hplen := p.length_of_loop_realization r hr
    have hsupport : p.support=r.vertices.toFinset := by rw [support,←hr,loop_support_eq]
    have hpath := traced_of_list r.head_eq r.last_eq r.consecutive
    have hamb : TracedWalk Adj r.start r.finish (r.vertices.length-1) r.vertices.toFinset := by
      obtain ⟨vs,hh,hl,hlen,hset,hw⟩ := hpath.asList
      have hwa : ListWalk Adj vs := listWalk_adj_of_sun hw
      have hh' := traced_of_list hh hl hwa
      simpa [hlen,hset] using hh'
    have hclosing : TracedWalk Adj r.finish r.start 1 {r.finish,r.start} :=
      TracedWalk.cons r.closing.1 (TracedWalk.nil r.start)
    have hall := hamb.append hclosing
    have hs : r.start∈r.vertices.toFinset := List.mem_toFinset.mpr (List.mem_of_head? r.head_eq)
    have hf : r.finish∈r.vertices.toFinset := List.mem_toFinset.mpr (List.mem_of_getLast? r.last_eq)
    have hlen : r.vertices.length-1+1=p.length := by
      have := r.nondegenerate
      unfold SimpleLoop.length at hplen
      omega
    have hs' : r.start∈p.support := hsupport.symm ▸ hs
    have hf' : r.finish∈p.support := hsupport.symm ▸ hf
    have htrace : TracedWalk Adj r.start r.start p.length p.support := by
      simpa [hlen,←hsupport,hs',hf'] using hall
    exact ⟨r.start,r.start,p.length,p.support,htrace,le_refl _,
      (fun w hw => p.loop_vertex_core hk hw),fun _ hw _ => hw⟩

lemma path_support_avoids_deeper_core (q : Polymer F) (hq : q.kind = .path)
    {d : ℕ} (hd : d+1≤200) (hshort : q.length≤4*(d+1)+2) :
    ∀w∈q.support,¬Core F (200-(d+1)) w := by
  have hr := q.realization
  rw [hq] at hr
  obtain ⟨r,hr⟩ := hr
  have hlen := q.length_of_path_realization r hr
  have hsupport : q.support=r.vertices.toFinset := by rw [support,←hr,path_support_eq]
  intro w hw hdeep
  rw [hsupport,List.mem_toFinset] at hw
  obtain ⟨i,hi,hw⟩ := List.mem_iff_getElem.mp hw
  have heq : r.vertex i=w := by simp only [BoundaryPath.vertex,List.getD_eq_getElem _ _ hi,hw]
  have hin : i≤r.length := by have := r.vertices_length; omega
  have hh := r.deeper_core_forces_length hd hin (heq.symm ▸ hdeep)
  omega

/-- An actual arbitrary root has a derived family of collar walks covering
every contact with any polymer confined outside the deeper core. -/
theorem ring_cover (p : Polymer F) {d K : ℕ} (hd : d≤4) (hK : K≤86) :
    ∃ parts : List (TracePiece (Ring F d)),
      (parts.map TracePiece.length).sum + K*parts.length ≤ p.length+K ∧
      ∀q:Polymer F, Incompatible p q →
        (∀w∈q.support,¬Core F (200-(d+1)) w) →
        ∃piece∈parts,¬Disjoint piece.support q.support := by
  obtain ⟨u,v,n,S,htrace,hn,hcore,hcontains⟩ := p.core_trace
  obtain ⟨parts,hbudget,hcover⟩ := core_trace_ring_cover hd hK htrace hcore
  refine ⟨parts,by omega,?_⟩
  intro q hinc hconf
  obtain ⟨w,hwp,hwq,hwcore⟩ := p.incompatible_core_contact q hinc
  obtain ⟨piece,hpiece,hw⟩ := hcover w (hcontains w hwp hwcore) ⟨hwcore,hconf w hwq⟩
  exact ⟨piece,hpiece,Finset.not_disjoint_iff.mpr ⟨w,hw,hwq⟩⟩

/-- The full arbitrary-root cover for every even short path length used by
the collar bound. Both confinement and the excursion charge are proved. -/
theorem short_even_ring_cover (p : Polymer F) (n : ℕ)
    (hmin : 8≤n) (hmax : n≤20) (heven : n%2=0) :
    ∃ parts : List (TracePiece (Ring F (n/4-1))),
      (parts.map TracePiece.length).sum + 2*(n-1+6*(n/4-1))*parts.length ≤
        p.length+2*(n-1+6*(n/4-1)) ∧
      ∀q:Polymer F,q.kind=.path→q.length=n→Incompatible p q→
        ∃piece∈parts,¬Disjoint piece.support q.support := by
  obtain ⟨parts,hbudget,hcover⟩ := p.ring_cover (d:=n/4-1) (K:=2*(n-1+6*(n/4-1)))
    (by omega) (by omega)
  refine ⟨parts,hbudget,?_⟩
  intro q hq hlen hinc
  apply hcover q hinc
  exact q.path_support_avoids_deeper_core hq (by omega) (by omega)

end Polymer
end RootedKP.AKLT
