import RootedKP.Polymers
import RootedKP.HoneycombSymmetry

namespace RootedKP.AKLT
open Honeycomb

theorem vertex_mem_of_traversal_edge {vs : List Vertex} {e : Edge} {x : Vertex}
    (he : e ∈ traversalEdges vs) (hx : x ∈ e) : x ∈ vs := by
  induction vs with
  | nil => simp [traversalEdges] at he
  | cons u rest ih =>
      cases rest with
      | nil => simp [traversalEdges] at he
      | cons v rest =>
          rcases Finset.mem_insert.mp he with rfl | he
          · simp only [Sym2.mem_iff] at hx
            simp only [List.mem_cons]
            exact hx.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))
          · exact List.mem_cons_of_mem u (ih he)

theorem traversalEdges_card {vs : List Vertex} (h : vs.Nodup) :
    (traversalEdges vs).card = vs.length - 1 := by
  induction vs with
  | nil => simp [traversalEdges]
  | cons u rest ih =>
      cases rest with
      | nil => simp [traversalEdges]
      | cons v rest =>
          have hn := List.nodup_cons.mp h
          have he : s(u, v) ∉ traversalEdges (v :: rest) :=
            fun he => hn.1 (vertex_mem_of_traversal_edge he (Sym2.mem_mk_left u v))
          rw [traversalEdges, Finset.card_insert_of_notMem he, ih hn.2]
          simp

theorem pathEdges_card {F : Rectangle} {s : ℕ} (p : BoundaryPath F s) :
    (pathEdges p).card = p.length := traversalEdges_card p.nodup

private theorem closing_not_mem (u v w : Vertex) (rest : List Vertex)
    (hn : (u :: v :: w :: rest).Nodup) {finish : Vertex}
    (ht : (u :: v :: w :: rest).getLast? = some finish) :
    s(finish, u) ∉ traversalEdges (u :: v :: w :: rest) := by
  have hu := (List.nodup_cons.mp hn).1
  have hv := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hfm : finish ∈ w :: rest := List.mem_of_getLast? (by simpa using ht)
  intro he
  rcases Finset.mem_insert.mp he with he | he
  · rcases Sym2.eq_iff.mp he with ⟨hfu, huv⟩ | ⟨hfv, huu⟩
    · exact hu (by simp [huv])
    · exact hv (hfv ▸ hfm)
  · exact hu (vertex_mem_of_traversal_edge he (Sym2.mem_mk_right finish u))

theorem loopEdges_card {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    (loopEdges p).card = p.length := by
  have hh := p.head_eq
  have ht := p.last_eq
  have hn := p.nodup
  have hl := p.nondegenerate
  cases heq : p.vertices with
  | nil => simp [heq] at hl
  | cons u rest =>
      cases rest with
      | nil => simp [heq] at hl
      | cons v rest =>
          cases rest with
          | nil => simp [heq] at hl
          | cons w rest =>
              have hs : u = p.start := by simpa [heq] using hh
              have hc := closing_not_mem u v w rest (by simpa [heq] using hn)
                (by simpa [heq] using ht)
              unfold loopEdges SimpleLoop.length
              rw [heq, ← hs, Finset.card_insert_of_notMem hc, traversalEdges_card (by simpa [heq] using hn)]
              simp

private theorem listWalk_sunWalk {F : Rectangle} {s : ℕ} {vs : List Vertex}
    {u v : Vertex} (hh : vs.head? = some u) (ht : vs.getLast? = some v)
    (hw : ListWalk (SunAdj F s) vs) : SunWalk F s u v (vs.length - 1) := by
  induction vs generalizing u with
  | nil => simp at hh
  | cons a rest ih =>
      have ha : a = u := by simpa using hh
      subst u
      cases rest with
      | nil =>
          have hv : a = v := by simpa using ht
          subst v
          exact SunWalk.nil a
      | cons b rest =>
          have tail := ih rfl (by simpa using ht) hw.2
          simpa using SunWalk.cons hw.1 tail

theorem boundaryPath_length_ge_three {F : Rectangle} {s : ℕ} (p : BoundaryPath F s) :
    3 ≤ p.length :=
  (listWalk_sunWalk p.head_eq p.last_eq p.consecutive).between_leaves_length
    p.start_leaf p.finish_leaf p.distinct

private theorem walk_snoc {u v w : Vertex} {n : ℕ} (h : Walk u v n) (he : Adj v w) :
    Walk u w (n + 1) := by
  induction h with
  | nil v => exact Walk.cons he (Walk.nil w)
  | cons huv hvw ih => exact Walk.cons huv (ih he)

theorem simpleLoop_length_even {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    p.length % 2 = 0 := by
  have h := walk_snoc (listWalk_sunWalk p.head_eq p.last_eq p.consecutive).toWalk p.closing.1
  have hp := h.closed_even
  have hl := p.nondegenerate
  unfold SimpleLoop.length
  have heq : p.vertices.length - 1 + 1 = p.vertices.length := by omega
  simpa [heq] using hp

theorem no_four_cycle {a b c d : Vertex}
    (hab : Adj a b) (hbc : Adj b c) (hcd : Adj c d) (hda : Adj d a)
    (hac : a ≠ c) : b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Adj] <;> omega

theorem simpleLoop_length_ne_four {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    p.length ≠ 4 := by
  intro hfour
  obtain ⟨a, b, c, d, heq⟩ := List.length_eq_four.mp hfour
  have hn : [a, b, c, d].Nodup := by simpa [heq] using p.nodup
  have hs : a = p.start := by simpa [heq] using p.head_eq
  have ht : d = p.finish := by simpa [heq] using p.last_eq
  have hw := p.consecutive
  simp only [heq, ListWalk] at hw
  have hda : Adj d a := by simpa [hs, ht] using p.closing.1
  have hac : a ≠ c := by
    intro hac
    exact (List.nodup_cons.mp hn).1 (by simp [hac])
  have hbd := no_four_cycle hw.1.1 hw.2.1.1 hw.2.2.1.1 hda hac
  exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [hbd])

theorem simpleLoop_length_ge_six {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) :
    6 ≤ p.length := by
  have hmin : 3 ≤ p.length := p.nondegenerate
  have heven := simpleLoop_length_even p
  have hfour := simpleLoop_length_ne_four p
  omega

namespace Polymer

theorem length_of_path_realization {F : Rectangle} (p : Polymer F)
    (q : BoundaryPath F haloRadius) (h : pathEdges q = p.edges) : p.length = q.length := by
  rw [length, ← h, pathEdges_card]

theorem length_of_loop_realization {F : Rectangle} (p : Polymer F)
    (q : SimpleLoop F haloRadius) (h : loopEdges q = p.edges) : p.length = q.length := by
  rw [length, ← h, loopEdges_card]

theorem path_length_ge_three {F : Rectangle} (p : Polymer F) (hk : p.kind = .path) :
    3 ≤ p.length := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨q, hq⟩ := hr
  rw [length_of_path_realization p q hq]
  exact boundaryPath_length_ge_three q

theorem loop_length_even {F : Rectangle} (p : Polymer F) (hk : p.kind = .loop) :
    p.length % 2 = 0 := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨q, hq⟩ := hr
  rw [length_of_loop_realization p q hq]
  exact simpleLoop_length_even q

theorem loop_length_ge_six {F : Rectangle} (p : Polymer F) (hk : p.kind = .loop) :
    6 ≤ p.length := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨q, hq⟩ := hr
  rw [length_of_loop_realization p q hq]
  exact simpleLoop_length_ge_six q

theorem length_ge_three {F : Rectangle} (p : Polymer F) : 3 ≤ p.length := by
  cases hk : p.kind with
  | path => exact path_length_ge_three p hk
  | loop =>
      have hr := p.realization
      rw [hk] at hr
      obtain ⟨q, hq⟩ := hr
      rw [length_of_loop_realization p q hq]
      exact q.nondegenerate

end Polymer
end RootedKP.AKLT
