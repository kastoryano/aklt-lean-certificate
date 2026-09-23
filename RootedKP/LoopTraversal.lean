import RootedKP.PolymerLength
import RootedKP.LoopTableLink
import Mathlib.Data.List.Chain

namespace RootedKP.AKLT
open Honeycomb Enumeration LoopCounts

set_option maxHeartbeats 0

lemma listWalk_iff_chain (E : Vertex → Vertex → Prop) (vs : List Vertex) :
    ListWalk E vs ↔ vs.IsChain E := by
  induction vs with
  | nil => simp [ListWalk]
  | cons u vs ih =>
    cases vs with
    | nil => simp [ListWalk]
    | cons v vs => simp [ListWalk, List.isChain_cons_cons, ih]

lemma listWalk_append_right {E : Vertex → Vertex → Prop} (xs ys : List Vertex)
    (h : ListWalk E (xs ++ ys)) : ListWalk E ys := by
  induction xs with
  | nil => exact h
  | cons u xs ih =>
    apply ih
    cases he : xs ++ ys with
    | nil => simp [he, ListWalk]
    | cons v rest =>
      have hh : ListWalk E (u :: v :: rest) := by simpa only [List.cons_append, he] using h
      simpa only [he] using hh.2

lemma extends_of_listWalk (seg trail : List Vertex)
    (hne : trail ≠ []) (hn : (seg ++ trail).Nodup)
    (hw : ListWalk Adj (seg ++ trail)) :
    Extends neighbors seg.length trail (seg ++ trail) := by
  induction seg using List.reverseRecOn generalizing trail with
  | nil => simpa using Extends.refl trail
  | append_singleton seg w ih =>
    cases trail with
    | nil => exact False.elim (hne rfl)
    | cons u us =>
      have hnod : (w :: u :: us).Nodup := by
        have hh : (seg ++ (w :: u :: us)).Nodup := by simpa [List.append_assoc] using hn
        exact (List.nodup_append.mp hh).2.1
      have hwalk : ListWalk Adj (w :: u :: us) :=
        listWalk_append_right seg _ (by simpa [List.append_assoc] using hw)
      have hrest := ih (w :: u :: us) (by simp)
        (by simpa [List.append_assoc] using hn) (by simpa [List.append_assoc] using hw)
      have he := Extends.step ((mem_neighbors u w).mpr (adj_symm hwalk.1))
        (List.nodup_cons.mp hnod).1 hrest
      simpa [List.length_append, List.append_assoc] using he

/-- The sublattice exchange fixes the anchored edge set and reverses its orientation. -/
def exchange : Vertex → Vertex
  | .a q r => .b (-q) (-r)
  | .b q r => .a (-q) (-r)

lemma exchange_involutive : Function.Involutive exchange := by
  intro v
  cases v <;> simp [exchange]

lemma exchange_adj_iff (u v : Vertex) : Adj (exchange u) (exchange v) ↔ Adj u v := by
  cases u <;> cases v <;> simp [exchange, Adj] <;> omega

/-- Directed edge transitivity, including both orientations. -/
theorem directed_edge_equiv {u v : Vertex} (h : Adj u v) :
    ∃ e : Vertex ≃ Vertex, e origin = u ∧ e first = v ∧
      ∀ x y, Adj (e x) (e y) ↔ Adj x y := by
  obtain ⟨q, r, k, hdir | hrev⟩ := edge_transitive h
  · let e := Equiv.ofBijective (edgeTransport q r k)
      ⟨edgeTransport_injective q r k, edgeTransport_surjective q r k⟩
    exact ⟨e, hdir.1, hdir.2, edgeTransport_adj_iff q r k⟩
  · let f := fun x => edgeTransport q r k (exchange x)
    have hi : Function.Injective f :=
      (edgeTransport_injective q r k).comp exchange_involutive.injective
    have hs : Function.Surjective f :=
      (edgeTransport_surjective q r k).comp exchange_involutive.surjective
    let e := Equiv.ofBijective f ⟨hi, hs⟩
    refine ⟨e, ?_, ?_, ?_⟩
    · simpa [e, f, origin, exchange] using hrev.2
    · simpa [e, f, first, exchange] using hrev.1
    · intro x y
      exact (edgeTransport_adj_iff q r k _ _).trans (exchange_adj_iff x y)

end RootedKP.AKLT

#print axioms RootedKP.AKLT.directed_edge_equiv
#print axioms RootedKP.AKLT.extends_of_listWalk
