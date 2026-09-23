import RootedKP.CyclicEdges
import RootedKP.FiniteRegion

namespace RootedKP.AKLT
open Honeycomb Enumeration LoopCounts
set_option maxHeartbeats 0

lemma listWalk_mono {E D : Vertex → Vertex → Prop} (h : ∀ u v, E u v → D u v)
    {vs : List Vertex} (hw : ListWalk E vs) : ListWalk D vs := by
  induction vs with
  | nil => trivial
  | cons u tail ih =>
    cases tail with
    | nil => trivial
    | cons v rest => exact ⟨h u v hw.1, ih hw.2⟩

lemma listWalk_map (f : Vertex → Vertex) {E D : Vertex → Vertex → Prop}
    (h : ∀ u v, E u v → D (f u) (f v)) {vs : List Vertex}
    (hw : ListWalk E vs) : ListWalk D (vs.map f) := by
  induction vs with
  | nil => trivial
  | cons u tail ih =>
    cases tail with
    | nil => trivial
    | cons v rest => exact ⟨h u v hw.1, ih hw.2⟩

lemma listWalk_reverse {E : Vertex → Vertex → Prop} (hs : ∀ u v, E u v → E v u)
    {vs : List Vertex} (hw : ListWalk E vs) : ListWalk E vs.reverse := by
  rw [listWalk_iff_chain, List.isChain_reverse, ← listWalk_iff_chain]
  exact listWalk_mono hs hw

/-- Every regional unoriented loop using a chosen directed edge has an anchored
traversal whose transported edge set recovers exactly that polymer. -/
theorem polymer_loop_encoding {F : Rectangle} {u v : Vertex}
    (e : Vertex ≃ Vertex) (hu : e origin = u) (hv : e first = v)
    (he : ∀ x y, Adj (e x) (e y) ↔ Adj x y)
    (p : Polymer F) (hk : p.kind = .loop) (hedge : s(u,v) ∈ p.edges) :
    ∃ result ∈ anchoredLoops p.length, cyclicEdges (result.map e) = p.edges := by
  have hr := p.realization
  rw [hk] at hr
  obtain ⟨q,hq⟩ := hr
  have hm : s(u,v) ∈ cyclicEdges q.vertices := by
    rwa [← loopEdges_eq_cyclicEdges, hq]
  obtain ⟨rest,hlen,hedges,hnod⟩ := cyclic_edge_oriented (by have := q.nondegenerate; omega) hm
  have hn := hnod q.nodup
  have hadj : ∀ a b, s(a,b) ∈ cyclicEdges (u :: v :: rest) → Adj a b := by
    intro a b hh
    rw [hedges] at hh
    exact (simpleLoop_cyclic_adj q a b hh).1
  have hw := listWalk_of_cyclic_adj hadj
  have hi : ∀ a b, Adj a b → Adj (e.symm a) (e.symm b) := by
    intro a b hh
    exact (he _ _).mp (by simpa using hh)
  have hmapped := listWalk_map e.symm hi hw
  have huw : e.symm u = origin := by rw [← hu]; simp
  have hvw : e.symm v = first := by rw [← hv]; simp
  have hnmap : ((u :: v :: rest).map e.symm).Nodup := hn.map e.symm.injective
  let result := ((u :: v :: rest).map e.symm).reverse
  have hresult : result = (rest.map e.symm).reverse ++ [first, origin] := by
    simp [result, huw, hvw, List.reverse_cons, List.append_assoc]
  have hex := extends_of_listWalk (rest.map e.symm).reverse [first,origin] (by simp)
    (by rw [← hresult]; exact List.nodup_reverse.mpr hnmap)
    (by rw [← hresult]; exact listWalk_reverse (fun _ _ => adj_symm) hmapped)
  have hlength : (rest.map e.symm).reverse.length = p.length - 2 := by
    rw [p.length_of_loop_realization q hq]
    unfold SimpleLoop.length
    simp only [List.length_reverse, List.length_map]
    simp only [List.length_cons] at hlen
    omega
  rw [hlength, ← hresult] at hex
  obtain ⟨z,hz⟩ : ∃ z, (u :: v :: rest).getLast? = some z := by
    cases heq : (u :: v :: rest).getLast? with
    | none => simp at heq
    | some z => exact ⟨z,rfl⟩
  have hzu : Adj z u := hadj z u (by
    rw [cyclicEdges_eq rfl hz]
    exact Finset.mem_insert_self ..)
  have hclose : closes result := by
    have hh : result.head? = some (e.symm z) := by
      simp only [result, List.head?_reverse, List.getLast?_map, hz, Option.map_some]
    cases hres : result with
    | nil => simp [hres] at hh
    | cons a tail =>
      have ha : a = e.symm z := by simpa [hres] using hh
      simpa [closes, ha, huw] using hi z u hzu
  refine ⟨result, (mem_anchoredLoops_iff _ _).mpr ⟨hex,hclose⟩, ?_⟩
  have hmap : result.map e = (u :: v :: rest).reverse := by
    simp [result, List.map_reverse, List.map_map, Function.comp_def]
  rw [hmap, cyclicEdges_reverse, hedges, ← loopEdges_eq_cyclicEdges, hq]

/-- Distinct canonical polymers cannot share a transported traversal code. -/
theorem polymer_eq_of_loop_code {F : Rectangle} (p q : Polymer F)
    (hp : p.kind = .loop) (hq : q.kind = .loop) (hedge : p.edges = q.edges) : p = q := by
  cases p
  cases q
  simp only at hp hq hedge
  cases hp
  cases hq
  cases hedge
  rfl

end RootedKP.AKLT
#print axioms RootedKP.AKLT.polymer_loop_encoding
