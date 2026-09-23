import RootedKP.ShortRootCharts
import RootedKP.LoopEncoding

/-! Passing from simple chart traversals to unoriented polymer edge sets.
Endpoint ordering picks one orientation; reversing the traversal preserves
both its support and its edge set. No factor of two is lost in this passage. -/
namespace RootedKP.ShortRootCharts
open Honeycomb BoundaryCharts Enumeration LoopCounts AKLT
set_option maxHeartbeats 0

theorem chart_extends_of_listWalk (C : Chart) (seg trail : List Vertex)
    (hne : trail ≠ []) (hn : (seg ++ trail).Nodup)
    (hw : ListWalk (BoundaryCharts.Adj C) (seg ++ trail)) :
    Extends (next C) seg.length trail (seg ++ trail) := by
  induction seg using List.reverseRecOn generalizing trail with
  | nil => simpa using Extends.refl trail
  | append_singleton seg w ih =>
    cases trail with
    | nil => exact False.elim (hne rfl)
    | cons u us =>
      have hnod : (w :: u :: us).Nodup := by
        have hh : (seg ++ (w :: u :: us)).Nodup := by simpa [List.append_assoc] using hn
        exact (List.nodup_append.mp hh).2.1
      have hwalk : ListWalk (BoundaryCharts.Adj C) (w :: u :: us) :=
        listWalk_append_right seg _ (by simpa [List.append_assoc] using hw)
      have hrest := ih (w :: u :: us) (by simp)
        (by simpa [List.append_assoc] using hn) (by simpa [List.append_assoc] using hw)
      have he := Extends.step ((mem_next C u w).mpr (BoundaryCharts.adj_symm hwalk.1))
        (List.nodup_cons.mp hnod).1 hrest
      simpa [List.length_append, List.append_assoc] using he

theorem chart_walk_to_extends (C : Chart) {vs : List Vertex} {start : Vertex}
    (ht : vs.getLast? = some start) (hn : vs.Nodup)
    (hw : ListWalk (BoundaryCharts.Adj C) vs) :
    Extends (next C) (vs.length - 1) [start] vs := by
  have hdecomp : vs.dropLast ++ [start] = vs :=
    List.dropLast_append_getLast? start (by rw [ht]; simp)
  have he := chart_extends_of_listWalk C vs.dropLast [start] (by simp)
    (by rwa [hdecomp]) (by rwa [hdecomp])
  simpa [hdecomp] using he

theorem leafBefore_total {u v : Vertex} (hu : Leaf .corner u) (hv : Leaf .corner v)
    (hne : u ≠ v) : leafBefore u v ∨ leafBefore v u := by
  have hu' := (leafCode_iff .corner u).mpr hu
  have hv' := (leafCode_iff .corner v).mpr hv
  cases u <;> cases v <;>
    simp_all [leafCode, upperLeaf, leftLeaf, leafBefore] <;> omega

/-- A literal chart path, with neither an orientation convention nor a finite
coordinate cutoff included in its specification. -/
structure Path (C : Chart) where
  vertices : List Vertex
  start : Vertex
  finish : Vertex
  head_eq : vertices.head? = some start
  last_eq : vertices.getLast? = some finish
  start_leaf : Leaf C start
  finish_leaf : Leaf C finish
  distinct : start ≠ finish
  nodup : vertices.Nodup
  consecutive : ListWalk (BoundaryCharts.Adj C) vertices

def Path.length {C : Chart} (p : Path C) : ℕ := p.vertices.length - 1
def Path.edges {C : Chart} (p : Path C) : Finset Edge := traversalEdges p.vertices

theorem Path.ordered_encoding (p : Path .corner) (root : Finset Vertex)
    (hit : hitsRoot root p.vertices) :
    ∃ trail, Traversal root p.length trail ∧ traversalEdges trail = p.edges := by
  rcases leafBefore_total p.start_leaf p.finish_leaf p.distinct with ho | ho
  · refine ⟨p.vertices.reverse, ?_, traversalEdges_reverse _⟩
    refine ⟨p.start, p.start_leaf, ?_, ?_⟩
    · simpa [Path.length] using chart_walk_to_extends .corner
        (by simpa using p.head_eq : p.vertices.reverse.getLast? = some p.start)
        (List.nodup_reverse.mpr p.nodup)
        (listWalk_reverse (fun _ _ => BoundaryCharts.adj_symm) p.consecutive)
    · constructor
      · have hh : p.vertices.reverse.head? = some p.finish := by simpa using p.last_eq
        cases heq : p.vertices.reverse with
        | nil => simp [heq] at hh
        | cons v vs =>
          have hv : v = p.finish := by simpa [heq] using hh
          exact ⟨hv ▸ (leafCode_iff .corner p.finish).mpr p.finish_leaf, hv ▸ ho⟩
      · simpa [hitsRoot] using hit
  · refine ⟨p.vertices, ?_, rfl⟩
    refine ⟨p.finish, p.finish_leaf, ?_, ?_⟩
    · exact chart_walk_to_extends .corner p.last_eq p.nodup p.consecutive
    · constructor
      · have hh := p.head_eq
        cases heq : p.vertices with
        | nil => simp [heq] at hh
        | cons v vs =>
          have hv : v = p.start := by simpa [heq] using hh
          exact ⟨hv ▸ (leafCode_iff .corner p.start).mpr p.start_leaf, hv ▸ ho⟩
      · exact hit

theorem Path.three_root_encoding (p : Path .corner)
    (hit : hitsRoot cornerRootThree p.vertices) :
    p.edges ∈ (paths cornerRootThree p.length).image traversalEdges := by
  obtain ⟨trail, ht, he⟩ := p.ordered_encoding cornerRootThree hit
  exact Finset.mem_image.mpr ⟨trail, (mem_paths_three_iff _ _).mpr ht, he⟩

/-- Any finite family of actual unoriented paths meeting the three-edge root
is bounded by the complete ordered search. The family contains edge sets,+not a choice of traversal or a direction for each polymer. -/
theorem edge_family_card_le (n : ℕ) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : Path .corner,
      p.length = n ∧ p.edges = e ∧ hitsRoot cornerRootThree p.vertices) :
    S.card ≤ count cornerRootThree n := by
  rw [count_eq_card]
  calc
    S.card ≤ ((paths cornerRootThree n).image traversalEdges).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨p, hp, rfl, hit⟩ := hS e he
      simpa [hp] using p.three_root_encoding hit
    _ ≤ (paths cornerRootThree n).card := Finset.card_image_le

end RootedKP.ShortRootCharts
