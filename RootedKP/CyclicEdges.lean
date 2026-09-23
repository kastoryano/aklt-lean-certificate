import RootedKP.LoopTraversal
import Mathlib.Data.List.Rotate

namespace RootedKP.AKLT
open Honeycomb Enumeration LoopCounts
set_option maxHeartbeats 0

def cyclicEdgeList (vs : List Vertex) : List Edge :=
  List.zipWith (fun u v => s(u,v)) vs (vs.rotate 1)

def cyclicEdges (vs : List Vertex) : Finset Edge := (cyclicEdgeList vs).toFinset

lemma zipEdges_close (vs : List Vertex) (u z : Vertex)
    (hz : vs.getLast? = some z) :
    (List.zipWith (fun a b => s(a,b)) vs (vs.tail ++ [u])).toFinset =
      insert s(z,u) (traversalEdges vs) := by
  induction vs with
  | nil => simp at hz
  | cons a rest ih =>
    cases rest with
    | nil => have he : a = z := by simpa using hz
             simp [he, traversalEdges]
    | cons b rest =>
      have h := ih (by simpa using hz)
      simpa [traversalEdges, Finset.insert_comm] using congrArg (fun t : Finset Edge => insert s(a,b) t) h

lemma cyclicEdges_eq {vs : List Vertex} {u z : Vertex}
    (hu : vs.head? = some u) (hz : vs.getLast? = some z) :
    cyclicEdges vs = insert s(z,u) (traversalEdges vs) := by
  cases vs with
  | nil => simp at hu
  | cons a rest =>
    have ha : a = u := by simpa using hu
    subst a
    simpa [cyclicEdges, cyclicEdgeList] using zipEdges_close (u :: rest) u z hz

lemma loopEdges_eq_cyclicEdges {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    loopEdges p = cyclicEdges p.vertices :=
  (cyclicEdges_eq p.head_eq p.last_eq).symm

lemma cyclicEdgeList_rotate (vs : List Vertex) (n : ℕ) :
    cyclicEdgeList (vs.rotate n) = (cyclicEdgeList vs).rotate n := by
  unfold cyclicEdgeList
  rw [List.zipWith_rotate_distrib _ _ _ n (by simp)]
  simp only [List.rotate_rotate]
  rw [Nat.add_comm n 1]

lemma cyclicEdges_rotate (vs : List Vertex) (n : ℕ) :
    cyclicEdges (vs.rotate n) = cyclicEdges vs := by
  rw [cyclicEdges, cyclicEdgeList_rotate]
  ext e
  simp [cyclicEdges, List.mem_rotate]

lemma cyclicEdgeList_length (vs : List Vertex) : (cyclicEdgeList vs).length = vs.length := by
  simp [cyclicEdgeList]

lemma cyclic_edge_reanchor {vs : List Vertex} {e : Edge}
    (hl : 2 ≤ vs.length) (he : e ∈ cyclicEdges vs) :
    ∃ n u v rest, vs.rotate n = u :: v :: rest ∧ s(u,v) = e := by
  have hm : e ∈ cyclicEdgeList vs := List.mem_toFinset.mp he
  obtain ⟨n, hn, heq⟩ := List.mem_iff_getElem.mp hm
  have hhead : ((cyclicEdgeList vs).rotate n).head? = some e := by
    rw [List.head?_rotate hn, List.getElem?_eq_getElem hn, heq]
  rw [← cyclicEdgeList_rotate] at hhead
  have hlen : 2 ≤ (vs.rotate n).length := by simpa using hl
  cases hv : vs.rotate n with
  | nil => simp [hv] at hlen
  | cons u tail =>
    cases tail with
    | nil => simp [hv] at hlen
    | cons v rest =>
      refine ⟨n, u, v, rest, hv, ?_⟩
      simpa [hv, cyclicEdgeList] using hhead

lemma traversalEdges_adj {E : Vertex → Vertex → Prop}
    (hs : ∀ u v, E u v → E v u) {vs : List Vertex} (hw : ListWalk E vs) :
    ∀ u v, s(u,v) ∈ traversalEdges vs → E u v := by
  induction vs with
  | nil => simp [traversalEdges]
  | cons a tail ih =>
    cases tail with
    | nil => simp [traversalEdges]
    | cons b rest =>
      intro u v he
      rcases Finset.mem_insert.mp he with he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hw.1
        · exact hs _ _ hw.1
      · exact ih hw.2 u v he

lemma simpleLoop_cyclic_adj {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    ∀ u v, s(u,v) ∈ cyclicEdges p.vertices → SunAdj F s u v := by
  rw [cyclicEdges_eq p.head_eq p.last_eq]
  intro u v he
  rcases Finset.mem_insert.mp he with he | he
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact p.closing
    · exact sunAdj_symm p.closing
  · exact traversalEdges_adj (fun _ _ => sunAdj_symm) p.consecutive u v he

lemma traversalEdges_subset_cyclicEdges {vs : List Vertex} :
    traversalEdges vs ⊆ cyclicEdges vs := by
  cases vs with
  | nil => simp [traversalEdges]
  | cons u rest =>
    obtain ⟨z,hz⟩ : ∃ z, (u :: rest).getLast? = some z := by
      cases he : (u :: rest).getLast? with
      | none => simp at he
      | some z => exact ⟨z,rfl⟩
    rw [cyclicEdges_eq rfl hz]
    exact Finset.subset_insert ..

lemma listWalk_of_cyclic_adj {E : Vertex → Vertex → Prop} {vs : List Vertex}
    (h : ∀ u v, s(u,v) ∈ cyclicEdges vs → E u v) : ListWalk E vs := by
  have hall : ∀ u v, s(u,v) ∈ traversalEdges vs → E u v :=
    fun u v he => h u v (traversalEdges_subset_cyclicEdges he)
  clear h
  induction vs with
  | nil => trivial
  | cons a tail ih =>
    cases tail with
    | nil => trivial
    | cons b rest =>
      exact ⟨hall a b (Finset.mem_insert_self ..),
        ih (fun u v he => hall u v (Finset.mem_insert_of_mem he))⟩

lemma traversalEdges_snoc {vs : List Vertex} {z : Vertex} (hz : vs.getLast? = some z)
    (u : Vertex) : traversalEdges (vs ++ [u]) = insert s(z,u) (traversalEdges vs) := by
  induction vs with
  | nil => simp at hz
  | cons a rest ih =>
    cases rest with
    | nil => have ha : a = z := by simpa using hz
             simp [ha, traversalEdges]
    | cons b rest =>
      have h := ih (by simpa using hz)
      simpa [traversalEdges, Finset.insert_comm] using
        congrArg (fun t : Finset Edge => insert s(a,b) t) h

lemma traversalEdges_reverse (vs : List Vertex) :
    traversalEdges vs.reverse = traversalEdges vs := by
  induction vs with
  | nil => simp [traversalEdges]
  | cons u rest ih =>
    cases rest with
    | nil => simp [traversalEdges]
    | cons v rest =>
      rw [List.reverse_cons, traversalEdges_snoc (by simp : (v :: rest).reverse.getLast? = some v), ih]
      simp [traversalEdges, Sym2.eq_swap]

lemma cyclicEdges_reverse (vs : List Vertex) : cyclicEdges vs.reverse = cyclicEdges vs := by
  cases vs with
  | nil => rfl
  | cons u rest =>
    obtain ⟨z,hz⟩ : ∃ z, (u :: rest).getLast? = some z := by
      cases he : (u :: rest).getLast? with
      | none => simp at he
      | some z => exact ⟨z,rfl⟩
    rw [cyclicEdges_eq (by rw [List.head?_reverse]; exact hz) (by simp : (u :: rest).reverse.getLast? = some u),
      cyclicEdges_eq rfl hz, traversalEdges_reverse]
    simp [Sym2.eq_swap]

/-- Reanchoring fixes the chosen edge's orientation; the output edge set is unchanged. -/
lemma cyclic_edge_oriented {vs : List Vertex} {u v : Vertex}
    (hl : 2 ≤ vs.length) (he : s(u,v) ∈ cyclicEdges vs) :
    ∃ rest, (u :: v :: rest).length = vs.length ∧
      cyclicEdges (u :: v :: rest) = cyclicEdges vs ∧
      (vs.Nodup → (u :: v :: rest).Nodup) := by
  obtain ⟨n,a,b,rest,hrot,heq⟩ := cyclic_edge_reanchor hl he
  have hlen : (a :: b :: rest).length = vs.length := by rw [← hrot]; simp
  have hedges : cyclicEdges (a :: b :: rest) = cyclicEdges vs := by
    rw [← hrot, cyclicEdges_rotate]
  have hnod : vs.Nodup → (a :: b :: rest).Nodup := by
    intro h
    rw [← hrot]
    exact List.nodup_rotate.mpr h
  rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨rest,hlen,hedges,hnod⟩
  · refine ⟨rest.reverse, by simpa using hlen, ?_, ?_⟩
    · have h := cyclicEdges_rotate (a :: b :: rest).reverse rest.length
      have hr : (a :: b :: rest).reverse.rotate rest.length = b :: a :: rest.reverse := by
        simpa [List.reverse_cons, List.append_assoc] using
          List.rotate_append_length_eq rest.reverse [b,a]
      rw [hr, cyclicEdges_reverse] at h
      exact h.trans hedges
    · intro hn
      have h := hnod hn
      simp only [List.nodup_cons, List.mem_cons, List.mem_reverse, List.nodup_reverse,
        not_or] at h ⊢
      exact ⟨⟨Ne.symm h.1.1,h.2.1⟩,h.1.2,h.2.2⟩

end RootedKP.AKLT
#print axioms RootedKP.AKLT.cyclic_edge_reanchor
