import RootedKP.ShortRootEdgeSets

namespace RootedKP.ShortRootCharts
open Honeycomb BoundaryCharts BoundaryCounts Enumeration AKLT
set_option maxHeartbeats 0

theorem extends_ambient_walk (C : Chart) {n : ℕ} {trail result : List Vertex}
    (he : Extends (next C) n trail result) :
    ∀ u us v vs, trail=u::us → result=v::vs → Walk u v n := by
  induction he with
  | refl trail =>
    intro u us v vs hu hv
    have : u=v := (List.cons.inj (hu.symm.trans hv)).1
    subst v
    exact Walk.nil u
  | @step u v us result n hv _ _ ih =>
    intro x xs y ys hx hy
    have hxu : x=u := (List.cons.inj hx.symm).1
    subst x
    exact Walk.cons ((mem_next C u v).mp hv).1 (ih v (u::us) y ys rfl hy)

theorem Path.ambient_walk {C : Chart} (p : Path C) : Walk p.finish p.start p.length := by
  have he := chart_walk_to_extends C p.last_eq p.nodup p.consecutive
  have hh := p.head_eq
  cases hvs : p.vertices with
  | nil => simp [hvs] at hh
  | cons u us =>
    have hu : u=p.start := by simpa [hvs] using hh
    subst u
    exact extends_ambient_walk C he p.finish [] p.start us rfl hvs

theorem odd_leaf_pairs {u v : Vertex} {n : ℕ} (hu : Leaf .corner u) (hv : Leaf .corner v)
    (hw : Walk u v n) (hn : n%2=1) :
    (upperLeaf u ∧ leftLeaf v) ∨ (leftLeaf u ∧ upperLeaf v) := by
  have hu' := (leafCode_iff .corner u).mpr hu
  have hv' := (leafCode_iff .corner v).mpr hv
  have hp := hw.heightQ_parity
  cases u <;> cases v <;>
    simp_all [leafCode,upperLeaf,leftLeaf,heightQ] <;> omega

/-- Every odd corner-chart path crosses the corner, with its unique
upper-to-left orientation represented by the complete corner search. -/
theorem Path.odd_encoding (p : Path .corner) (hn : p.length%2=1) :
    ∃ trail ∈ cornerPaths p.length, traversalEdges trail = p.edges := by
  have hp := odd_leaf_pairs p.finish_leaf p.start_leaf p.ambient_walk hn
  rcases hp with ⟨hfinish,hstart⟩ | ⟨hfinish,hstart⟩
  · refine ⟨p.vertices,?_,rfl⟩
    apply (mem_cornerPaths_iff _ _).mpr
    cases hf : p.finish with
    | b q r => simp [hf,upperLeaf] at hfinish
    | a q r =>
      have hq : -1≤q ∧ r=1 := by simpa [hf,upperLeaf] using hfinish
      obtain ⟨hq,rfl⟩ := hq
      refine ⟨q,hq,?_,?_⟩
      · simpa [hf,Path.length] using chart_walk_to_extends .corner p.last_eq p.nodup p.consecutive
      · have hh := p.head_eq
        cases hvs : p.vertices with
        | nil => simp [hvs] at hh
        | cons v vs =>
          have hv : v=p.start := by simpa [hvs] using hh
          exact hv ▸ hstart
  · refine ⟨p.vertices.reverse,?_,traversalEdges_reverse _⟩
    apply (mem_cornerPaths_iff _ _).mpr
    cases hs : p.start with
    | b q r => simp [hs,upperLeaf] at hstart
    | a q r =>
      have hq : -1≤q ∧ r=1 := by simpa [hs,upperLeaf] using hstart
      obtain ⟨hq,rfl⟩ := hq
      refine ⟨q,hq,?_,?_⟩
      · have hl : p.vertices.reverse.getLast?=some p.start := by simpa using p.head_eq
        simpa [hs,Path.length] using chart_walk_to_extends .corner hl
          (List.nodup_reverse.mpr p.nodup)
          (listWalk_reverse (fun _ _ => BoundaryCharts.adj_symm) p.consecutive)
      · have hh : p.vertices.reverse.head?=some p.finish := by simpa using p.last_eq
        cases hvs : p.vertices.reverse with
        | nil => simp [hvs] at hh
        | cons v vs =>
          have hv : v=p.finish := by simpa [hvs] using hh
          exact hv ▸ hfinish

theorem odd_edge_family_card_le (n : ℕ) (hn : n%2=1) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : Path .corner, p.length=n ∧ p.edges=e) :
    S.card ≤ cornerCount n := by
  rw [cornerCount_eq_card]
  calc
    S.card ≤ ((cornerPaths n).image traversalEdges).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨p,hp,rfl⟩ := hS e he
      obtain ⟨trail,ht,he⟩ := p.odd_encoding (by simpa [hp] using hn)
      exact Finset.mem_image.mpr ⟨trail,by simpa [hp] using ht,he⟩
    _ ≤ (cornerPaths n).card := Finset.card_image_le

end RootedKP.ShortRootCharts
