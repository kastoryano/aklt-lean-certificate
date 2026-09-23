import RootedKP.BoundaryCharts

namespace RootedKP.BoundaryCharts
open Honeycomb

theorem next_of_core {C : Chart} {u : Vertex} (h : core C u) : next C u = neighbors u := by
  ext v
  simp [next, h]

def leafCode : Chart → Vertex → Prop
  | .bulk, _ => False
  | .side, .a q _ => q = 1
  | .side, .b _ _ => False
  | .corner, v => upperLeaf v ∨ leftLeaf v

instance (C : Chart) (v : Vertex) : Decidable (leafCode C v) := by
  cases C <;> cases v <;> unfold leafCode upperLeaf leftLeaf <;> infer_instance

theorem leafCode_iff (C : Chart) (u : Vertex) : leafCode C u ↔ Leaf C u := by
  by_cases hc : core C u
  · rw [Leaf, next_of_core hc, neighbors_card]
    cases C <;> cases u <;> simp_all [core, leafCode, upperLeaf, leftLeaf] <;> omega
  · cases C with
    | bulk => cases u <;> exact False.elim (hc trivial)
    | side =>
      cases u with
      | a q r =>
        by_cases hq : q = 1
        · subst q
          have hn : next .side (.a 1 r) = {.b 0 r} := by
            ext v
            cases v <;> simp [Adj, Honeycomb.Adj, core] <;> omega
          simp [leafCode, Leaf, hn]
        · have hn : next .side (.a q r) = ∅ := by
            ext v
            cases v <;> simp [Adj, Honeycomb.Adj, core] <;> simp [core] at hc <;> omega
          simp [leafCode, Leaf, hn, hq]
      | b q r =>
        have hn : next .side (.b q r) = ∅ := by
          ext v
          cases v <;> simp [Adj, Honeycomb.Adj, core] <;> simp [core] at hc <;> omega
        simp [leafCode, Leaf, hn]
    | corner =>
      cases u with
      | a q r =>
        by_cases hu : upperLeaf (.a q r)
        · exact ⟨fun _ => upperLeaf_is_leaf hu, fun _ => Or.inl hu⟩
        · have hn : next .corner (.a q r) = ∅ := by
            ext v
            cases v <;> simp [Adj, Honeycomb.Adj, core] <;>
              simp [core, upperLeaf] at hc hu <;> omega
          simp [leafCode, Leaf, hn, hu, leftLeaf]
      | b q r =>
        by_cases hl : leftLeaf (.b q r)
        · exact ⟨fun _ => leftLeaf_is_leaf hl, fun _ => Or.inr hl⟩
        · have hn : next .corner (.b q r) = ∅ := by
            ext v
            cases v <;> simp [Adj, Honeycomb.Adj, core] <;>
              simp [core, leftLeaf] at hc hl <;> omega
          simp [leafCode, Leaf, hn, hl, upperLeaf]

end RootedKP.BoundaryCharts
