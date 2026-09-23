import RootedKP.RegionalEndpointBounds
import RootedKP.LoopEncoding

/-! Splitting unoriented boundary paths at a specified edge. The encoding
counts edge sets, so it does not introduce a traversal-orientation factor. -/
namespace RootedKP.AKLT
open Honeycomb RegionalEndpoints Enumeration BoundaryCounts
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

lemma regional_extends_of_listWalk (F : Rectangle) (seg trail : List Vertex)
    (hne : trail ≠ []) (hn : (seg ++ trail).Nodup)
    (hw : ListWalk (SunAdj F 200) (seg ++ trail)) :
    Extends (RegionalEndpoints.next F) seg.length trail (seg ++ trail) := by
  induction seg using List.reverseRecOn generalizing trail with
  | nil => simpa using Extends.refl trail
  | append_singleton seg w ih =>
    cases trail with
    | nil => exact False.elim (hne rfl)
    | cons u us =>
      have hnod : (w :: u :: us).Nodup := by
        have hh : (seg ++ (w :: u :: us)).Nodup := by simpa [List.append_assoc] using hn
        exact (List.nodup_append.mp hh).2.1
      have hwalk : ListWalk (SunAdj F 200) (w :: u :: us) :=
        listWalk_append_right seg _ (by simpa [List.append_assoc] using hw)
      have hrest := ih (w :: u :: us) (by simp)
        (by simpa [List.append_assoc] using hn) (by simpa [List.append_assoc] using hw)
      have he := Extends.step ((RegionalEndpoints.mem_next F u w).mpr (sunAdj_symm hwalk.1))
        (List.nodup_cons.mp hnod).1 hrest
      simpa [List.length_append, List.append_assoc] using he

lemma arm_mem_prefixes (F : Rectangle) (seg : List Vertex) (w u forbidden : Vertex)
    (hn : (seg ++ [w,u]).Nodup)
    (hw : ListWalk (SunAdj F 200) (seg ++ [w,u]))
    (hleaf : endsAt (Leaf F 200) (seg ++ [w,u]))
    (hf : forbidden ∉ seg ++ [w,u]) :
    seg ++ [w,u] ∈ prefixes F (seg.length+1) u forbidden := by
  apply Finset.mem_biUnion.mpr
  refine ⟨w, Finset.mem_erase.mpr ⟨?_, ?_⟩, Finset.mem_filter.mpr ⟨?_, hleaf⟩⟩
  · intro h
    exact hf (by simp [← h])
  · exact (RegionalEndpoints.mem_next F u w).mpr
      (sunAdj_symm (listWalk_append_right seg [w,u] hw).1)
  · exact (mem_extensions_iff _ _ _ _).mpr
      (regional_extends_of_listWalk F seg [w,u] (by simp) hn hw)

lemma mem_traversalEdges_split {vs : List Vertex} {u v : Vertex}
    (he : s(u,v) ∈ traversalEdges vs) :
    ∃ pre post, vs = pre ++ u :: v :: post ∨ vs = pre ++ v :: u :: post := by
  induction vs with
  | nil => simp [traversalEdges] at he
  | cons a rest ih =>
    cases rest with
    | nil => simp [traversalEdges] at he
    | cons b rest =>
      rcases Finset.mem_insert.mp he with he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨[],rest,Or.inl rfl⟩
        · exact ⟨[],rest,Or.inr rfl⟩
      · obtain ⟨pre,post,h | h⟩ := ih he
        · exact ⟨a::pre,post,Or.inl (by simp only [List.cons_append,h])⟩
        · exact ⟨a::pre,post,Or.inr (by simp only [List.cons_append,h])⟩

lemma traversalEdges_split (pre post : List Vertex) (u v : Vertex) :
    traversalEdges (pre ++ u :: v :: post) =
      insert s(u,v) (traversalEdges (pre ++ [u]) ∪ traversalEdges (v :: post)) := by
  induction pre with
  | nil => simp [traversalEdges]
  | cons a pre ih =>
    cases pre with
    | nil => simp [traversalEdges, Finset.insert_comm]
    | cons b pre =>
      simp only [List.cons_append, traversalEdges] at ih ⊢
      rw [ih]
      ext e
      simp only [Finset.mem_insert, Finset.mem_union]
      tauto

/-- A simple boundary traversal with orientation suppressed. -/
structure BoundaryTraversal (F : Rectangle) (vs : List Vertex) : Prop where
  nodup : vs.Nodup
  consecutive : ListWalk (SunAdj F 200) vs
  first_leaf : endsAt (Leaf F 200) vs
  last_leaf : endsAt (Leaf F 200) vs.reverse

lemma BoundaryTraversal.reverse {F : Rectangle} {vs : List Vertex}
    (h : BoundaryTraversal F vs) : BoundaryTraversal F vs.reverse := by
  exact ⟨List.nodup_reverse.mpr h.nodup,
    listWalk_reverse (fun _ _ => sunAdj_symm) h.consecutive,
    h.last_leaf, by simpa using h.first_leaf⟩

lemma boundaryPath_traversal {F : Rectangle} (p : BoundaryPath F 200) :
    BoundaryTraversal F p.vertices := by
  refine ⟨p.nodup,p.consecutive,?_,?_⟩
  · have hh := p.head_eq
    cases he : p.vertices with
    | nil => simp [he] at hh
    | cons v vs => exact (by simpa [he] using hh : v = p.start) ▸ p.start_leaf
  · have hh : p.vertices.reverse.head? = some p.finish := by simpa using p.last_eq
    cases he : p.vertices.reverse with
    | nil => simp [he] at hh
    | cons v vs => exact (by simpa only [he, List.head?_cons, Option.some.injEq] using hh : v = p.finish) ▸ p.finish_leaf

lemma oriented_boundary_split {F : Rectangle} {vs : List Vertex} {u v : Vertex}
    (hb : BoundaryTraversal F vs) (he : s(u,v) ∈ traversalEdges vs) :
    ∃ pre post, BoundaryTraversal F (pre ++ u :: v :: post) ∧
      traversalEdges (pre ++ u :: v :: post) = traversalEdges vs ∧
      (pre ++ u :: v :: post).length = vs.length := by
  obtain ⟨pre,post,h | h⟩ := mem_traversalEdges_split he
  · exact ⟨pre,post,h ▸ hb,h ▸ rfl,h ▸ rfl⟩
  · have hr : vs.reverse = post.reverse ++ u :: v :: pre.reverse := by
      simp [h, List.reverse_append, List.reverse_cons, List.append_assoc]
    refine ⟨post.reverse,pre.reverse,?_,?_,?_⟩
    · rw [← hr]
      exact hb.reverse
    · rw [← hr, traversalEdges_reverse]
    · rw [← hr, List.length_reverse]

lemma listWalk_append_left {E : Vertex → Vertex → Prop} (xs ys : List Vertex)
    (h : ListWalk E (xs ++ ys)) : ListWalk E xs :=
  (listWalk_iff_chain E xs).mpr ((listWalk_iff_chain E _).mp h).left_of_append

lemma BoundaryTraversal.left_arm {F : Rectangle} {pre post : List Vertex} {u v : Vertex}
    (hb : BoundaryTraversal F (pre ++ u :: v :: post)) (hne : pre ≠ []) :
    pre ++ [u] ∈ prefixes F pre.length u v := by
  have hex : ∃ seg w, pre = seg ++ [w] := by
    cases he : pre.reverse with
    | nil => exact False.elim (hne (List.reverse_eq_nil_iff.mp he))
    | cons w rest =>
      refine ⟨rest.reverse,w,?_⟩
      simpa using congrArg List.reverse he
  obtain ⟨seg,w,rfl⟩ := hex
  have hd : ((seg ++ [w,u]) ++ (v :: post)).Nodup := by
    simpa [List.append_assoc] using hb.nodup
  have hn := (List.nodup_append.mp hd).1
  have hf : v ∉ seg ++ [w,u] := by
    intro hm
    exact (List.nodup_append.mp hd).2.2 v hm v (by simp) rfl
  have hw : ListWalk (SunAdj F 200) (seg ++ [w,u]) :=
    listWalk_append_left _ _ (by simpa [List.append_assoc] using hb.consecutive)
  have hl : endsAt (Leaf F 200) (seg ++ [w,u]) := by
    cases seg with
    | nil => exact hb.first_leaf
    | cons a seg => exact hb.first_leaf
  simpa [List.append_assoc] using arm_mem_prefixes F seg w u v hn hw hl hf

lemma BoundaryTraversal.right_arm {F : Rectangle} {pre post : List Vertex} {u v : Vertex}
    (hb : BoundaryTraversal F (pre ++ u :: v :: post)) (hne : post ≠ []) :
    (v :: post).reverse ∈ prefixes F post.length v u := by
  have hr : (pre ++ u :: v :: post).reverse = post.reverse ++ v :: u :: pre.reverse := by
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have hb' : BoundaryTraversal F (post.reverse ++ v :: u :: pre.reverse) := hr ▸ hb.reverse
  simpa using hb'.left_arm (by simpa using hne)

lemma BoundaryTraversal.split_code {F : Rectangle} {pre post : List Vertex} {u v : Vertex}
    (hb : BoundaryTraversal F (pre ++ u :: v :: post))
    (hu : Core F 200 u) (hv : Core F 200 v) :
    1 ≤ pre.length ∧ 1 ≤ post.length ∧
      pre ++ [u] ∈ prefixes F pre.length u v ∧
      (v :: post).reverse ∈ prefixes F post.length v u := by
  have hl : pre ≠ [] := by
    intro he
    subst pre
    exact core_not_leaf hu hb.first_leaf
  have hr : post ≠ [] := by
    intro he
    subst post
    have hh := hb.last_leaf
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_assoc] at hh
    exact core_not_leaf hv hh
  refine ⟨?_,?_,hb.left_arm hl,hb.right_arm hr⟩
  · have := List.length_pos_iff.mpr hl
    omega
  · have := List.length_pos_iff.mpr hr
    omega

/-- All possible reconstructed edge sets obtained by independently choosing
left and right endpoint arms. Colliding arms merely enlarge this upper bound. -/
def edgeArmSets (F : Rectangle) (n : ℕ) (u v : Vertex) : Finset (Finset Edge) :=
  (Finset.range (n-2)).biUnion fun i =>
    ((prefixes F (i+1) u v) ×ˢ (prefixes F (n-2-i) v u)).image
      (fun arms => insert s(u,v) (traversalEdges arms.1 ∪ traversalEdges arms.2))

lemma edgeArmSets_card_le (F : Rectangle) (n : ℕ) (u v : Vertex) :
    (edgeArmSets F n u v).card ≤
      ∑ i ∈ Finset.range (n-2), count F (i+1) u v * count F (n-2-i) v u := by
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ((prefixes F (i+1) u v) ×ˢ (prefixes F (n-2-i) v u)).card :=
      Finset.card_image_le
    _ = _ := by rw [Finset.card_product, ← count_eq_card, ← count_eq_card]

lemma boundaryPath_mem_edgeArmSets {F : Rectangle} (p : BoundaryPath F 200)
    {u v : Vertex} (hu : Core F 200 u) (hv : Core F 200 v)
    (he : s(u,v) ∈ pathEdges p) :
    pathEdges p ∈ edgeArmSets F p.length u v := by
  obtain ⟨pre,post,hb,heq,hlen⟩ := oriented_boundary_split (boundaryPath_traversal p) he
  obtain ⟨hpre,hpost,hl,hr⟩ := hb.split_code hu hv
  have hlen' : pre.length + post.length + 1 = p.length := by
    simp only [List.length_append, List.length_cons] at hlen
    unfold BoundaryPath.length
    omega
  have hi : pre.length-1 < p.length-2 := by omega
  have hil : pre.length-1+1 = pre.length := by omega
  have hir : p.length-2-(pre.length-1) = post.length := by omega
  apply Finset.mem_biUnion.mpr
  refine ⟨pre.length-1,Finset.mem_range.mpr hi, Finset.mem_image.mpr ?_⟩
  refine ⟨(pre ++ [u],(v::post).reverse), Finset.mem_product.mpr ?_, ?_⟩
  · simpa only [hil,hir] using And.intro hl hr
  · simpa only [traversalEdges_reverse, ← traversalEdges_split, pathEdges] using heq

/-- Canonical unoriented edge-set count at a fixed interior edge. -/
theorem interior_edge_family_card_le (F : Rectangle) (n : ℕ) (u v : Vertex)
    (hu : Core F 200 u) (hv : Core F 200 v) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length = n ∧ pathEdges p = e ∧ s(u,v) ∈ e) :
    S.card ≤ ∑ i ∈ Finset.range (n-2), count F (i+1) u v * count F (n-2-i) v u := by
  apply (Finset.card_le_card (t := edgeArmSets F n u v) ?_).trans
    (edgeArmSets_card_le F n u v)
  intro e he
  obtain ⟨p,hlen,rfl,hedge⟩ := hS e he
  simpa only [hlen] using boundaryPath_mem_edgeArmSets p hu hv hedge

theorem interior_edge_family_convolution (F : Rectangle) (n : ℕ) (hn : 21 ≤ n)
    (u v : Vertex) (hadj : SunAdj F 200 u v)
    (hu : Core F 200 u) (hv : Core F 200 v) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length = n ∧ pathEdges p = e ∧ s(u,v) ∈ e) :
    (S.card : ℚ) ≤ (2*(n:ℚ)+95)*2^n/1024 := by
  have h := interior_edge_family_card_le F n u v hu hv S hS
  have hcast : (S.card : ℚ) ≤
      ∑ i ∈ Finset.range (n-2), (count F (i+1) u v : ℚ) * count F (n-2-i) v u := by
    exact_mod_cast h
  exact hcast.trans (two_arm_convolution F n hn u v ((RegionalEndpoints.mem_next F u v).mpr hadj))

lemma BoundaryTraversal.leaf_split_prefix_nil {F : Rectangle}
    {pre post : List Vertex} {u v : Vertex}
    (hb : BoundaryTraversal F (pre ++ u :: v :: post)) (hu : Leaf F 200 u) :
    pre = [] := by
  by_contra hne
  have hdecomp : pre.dropLast ++ [pre.getLast hne] = pre := List.dropLast_concat_getLast hne
  let w := pre.getLast hne
  have hw : ListWalk (SunAdj F 200) (w :: u :: v :: post) :=
    listWalk_append_right pre.dropLast _ (by
      have hh := hb.consecutive
      rw [← hdecomp] at hh
      simpa only [List.append_assoc,List.singleton_append] using hh)
  have hnod : (w :: u :: v :: post).Nodup := by
    have hh : (pre.dropLast ++ (w :: u :: v :: post)).Nodup := by
      have hh := hb.nodup
      rw [← hdecomp] at hh
      simpa only [List.append_assoc,List.singleton_append] using hh
    exact (List.nodup_append.mp hh).2.1
  have hnc := leaf_not_core hu
  have huw := sunAdj_symm hw.1
  have huv := hw.2.1
  have heq := noncore_core_neighbor_unique hnc
    (huw.2.resolve_left hnc) (huv.2.resolve_left hnc) huw.1 huv.1
  exact (List.nodup_cons.mp hnod).1 (by simp [heq])

lemma boundaryPath_mem_boundaryArmSets {F : Rectangle} (p : BoundaryPath F 200)
    {u v : Vertex} (hu : Leaf F 200 u) (hv : Core F 200 v)
    (he : s(u,v) ∈ pathEdges p) :
    pathEdges p ∈ (prefixes F (p.length-1) v u).image
      (fun arm => insert s(u,v) (traversalEdges arm)) := by
  obtain ⟨pre,post,hb,heq,hlen⟩ := oriented_boundary_split (boundaryPath_traversal p) he
  have hnil := hb.leaf_split_prefix_nil hu
  subst pre
  have hpost : post ≠ [] := by
    intro hh
    subst post
    exact core_not_leaf hv hb.last_leaf
  have hr := hb.right_arm hpost
  have hlen' : post.length = p.length-1 := by
    simp only [List.nil_append,List.length_cons] at hlen
    have := boundaryPath_length_ge_three p
    unfold BoundaryPath.length at *
    omega
  refine Finset.mem_image.mpr ⟨(v::post).reverse,?_,?_⟩
  · simpa only [hlen'] using hr
  · simpa only [List.nil_append,traversalEdges,traversalEdges_reverse,pathEdges] using heq

/-- At a fixed leaf prong only one endpoint arm is needed. -/
theorem boundary_edge_family_card_le (F : Rectangle) (n : ℕ) (u v : Vertex)
    (hu : Leaf F 200 u) (hv : Core F 200 v) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length = n ∧ pathEdges p = e ∧ s(u,v) ∈ e) :
    S.card ≤ count F (n-1) v u := by
  rw [count_eq_card]
  apply (Finset.card_le_card (t := (prefixes F (n-1) v u).image
    (fun arm => insert s(u,v) (traversalEdges arm))) ?_).trans Finset.card_image_le
  intro e he
  obtain ⟨p,hlen,rfl,hedge⟩ := hS e he
  simpa only [hlen] using boundaryPath_mem_boundaryArmSets p hu hv hedge

theorem boundary_edge_family_long (F : Rectangle) (n : ℕ) (hn : 11 ≤ n)
    (u v : Vertex) (hadj : SunAdj F 200 u v)
    (hu : Leaf F 200 u) (hv : Core F 200 v) (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length = n ∧ pathEdges p = e ∧ s(u,v) ∈ e) :
    S.card ≤ 2^(n-5) := by
  have h := boundary_edge_family_card_le F n u v hu hv S hS
  have hg := count_long F (n-1) (by omega) v u
    ((RegionalEndpoints.mem_next F v u).mpr (sunAdj_symm hadj))
  exact h.trans (by simpa [Nat.sub_sub] using hg)

end
end RootedKP.AKLT
#print axioms RootedKP.AKLT.interior_edge_family_convolution

#print axioms RootedKP.AKLT.boundary_edge_family_long
