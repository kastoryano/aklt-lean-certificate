import RootedKP.RegionalChartPolymers
import RootedKP.BoundaryLeaves
import RootedKP.BoundaryCountsTable

/-! Any regional path between two leaves on one side embeds globally into
the infinite straight-side chart. Fixing the larger leaf parameter gives
exactly the orientation counted by the verified R(n) search. -/
namespace RootedKP.Honeycomb
open AKLT BoundaryCounts Enumeration
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

namespace RegionalSide

def reflect : Vertex → Vertex
  | .a q r => .a q (1-q-r)
  | .b q r => .b q (-q-r)

lemma reflect_involutive : Function.Involutive reflect := by
  intro v
  cases v <;> simp [reflect]

lemma reflect_adj {u v : Vertex} (h : Adj u v) : Adj (reflect u) (reflect v) := by
  cases u <;> cases v <;> simp_all [Adj,reflect] <;> omega

lemma toChart_injective (i : Fin 6) : Function.Injective (toChart i) := by
  intro u v h
  fin_cases i <;> cases u <;> cases v <;>
    simp only [toChart,inverseRotate,Vertex.a.injEq,Vertex.b.injEq,
      reduceCtorEq] at h ⊢ <;> omega

def map (F : Rectangle) (i : Fin 6) (right : ℤ) (v : Vertex) : Vertex :=
  reflect (translate (-(sideChart F 200 i).Q) (-right) (toChart i v))

lemma map_injective (F : Rectangle) (i : Fin 6) (right : ℤ) :
    Function.Injective (map F i right) :=
  reflect_involutive.injective.comp
    ((translate_injective _ _).comp (toChart_injective i))

lemma map_leaf (F : Rectangle) (i : Fin 6) (right r : ℤ) :
    map F i right (BoundaryLeaves.leaf F i r) = .a 1 (right-r) := by
  simp [map,BoundaryLeaves.leaf,toChart_fromChart,translate,reflect]
  ring

lemma map_core {F : Rectangle} (i : Fin 6) (right : ℤ) {v : Vertex}
    (hc : Core F 200 v) : BoundaryCharts.core .side (map F i right v) := by
  fin_cases i <;> cases v <;>
    simp only [map,reflect,translate,toChart,inverseRotate,sideChart,BoundaryCharts.core] <;>
    simp only [core_a_coordinates,core_b_coordinates] at hc <;> omega

lemma map_adj {F : Rectangle} (i : Fin 6) (right : ℤ) {u v : Vertex}
    (h : SunAdj F 200 u v) : BoundaryCharts.Adj .side (map F i right u) (map F i right v) := by
  refine ⟨reflect_adj (translate_adj _ _ (toChart_adj i h.1)),?_⟩
  exact h.2.elim (fun hu => Or.inl (map_core i right hu))
    (fun hv => Or.inr (map_core i right hv))

lemma mapped_walk {F : Rectangle} (i : Fin 6) (right : ℤ) {vs : List Vertex}
    (hw : ListWalk (SunAdj F 200) vs) :
    ListWalk (BoundaryCharts.Adj .side) (vs.map (map F i right)) := by
  induction vs with
  | nil => trivial
  | cons u rest ih =>
    cases rest with
    | nil => trivial
    | cons v rest => exact ⟨map_adj i right hw.1,ih hw.2⟩

lemma traversalEdges_map (f : Vertex → Vertex) (vs : List Vertex) :
    traversalEdges (vs.map f) = (traversalEdges vs).image (Sym2.map f) := by
  induction vs with
  | nil => rfl
  | cons u rest ih =>
    cases rest with
    | nil => rfl
    | cons v rest =>
      simpa only [List.map_cons,traversalEdges,Finset.image_insert,Sym2.map_mk]
        using congrArg (insert s(f u,f v)) ih

lemma mapEdge_injective {f : Vertex → Vertex} (hf : Function.Injective f) :
    Function.Injective (Sym2.map f) := by
  intro e d h
  induction e using Sym2.inductionOn with
  | hf u v =>
    induction d using Sym2.inductionOn with
    | hf x y =>
      simp only [Sym2.map_mk,Sym2.eq_iff] at h ⊢
      rcases h with ⟨hux,hvy⟩ | ⟨huy,hvx⟩
      · exact Or.inl ⟨hf hux,hf hvy⟩
      · exact Or.inr ⟨hf huy,hf hvx⟩

lemma mapEdgeSets_injective (F : Rectangle) (i : Fin 6) (right : ℤ) :
    Function.Injective (Finset.image (Sym2.map (map F i right))) := by
  intro s t h
  exact Finset.image_injective (mapEdge_injective (map_injective F i right)) h

lemma encode_oriented {F : Rectangle} (i : Fin 6) (left right : ℤ) (hlt : left < right)
    (vs : List Vertex) (hw : ListWalk (SunAdj F 200) vs) (hn : vs.Nodup)
    (hh : vs.head? = some (BoundaryLeaves.leaf F i left))
    (ht : vs.getLast? = some (BoundaryLeaves.leaf F i right)) :
    vs.map (map F i right) ∈ sidePaths (vs.length-1) := by
  apply (mem_sidePaths_iff _ _).mpr
  constructor
  · have ht' : (vs.map (map F i right)).getLast? = some (.a 1 0) := by
      simpa only [List.getLast?_map,ht,Option.map_some,map_leaf,sub_self]
    have he := ShortRootCharts.chart_walk_to_extends .side ht'
      (hn.map (map_injective F i right)) (mapped_walk i right hw)
    simpa only [List.length_map] using he
  · have hh' : (vs.map (map F i right)).head? = some (.a 1 (right-left)) := by
      simpa only [List.head?_map,hh,Option.map_some,map_leaf]
    cases hvs : vs.map (map F i right) with
    | nil => simp [hvs] at hh'
    | cons v tail =>
      have hv : v = .a 1 (right-left) := by simpa only [hvs,List.head?_cons,Option.some.injEq] using hh'
      change sideAbove v
      rw [hv]
      exact ⟨rfl,by omega⟩

lemma path_encoding {F : Rectangle} (p : BoundaryPath F 200)
    (i : Fin 6) (left right : ℤ) (hlt : left < right)
    (he : (p.start = BoundaryLeaves.leaf F i left ∧ p.finish = BoundaryLeaves.leaf F i right) ∨
      (p.finish = BoundaryLeaves.leaf F i left ∧ p.start = BoundaryLeaves.leaf F i right)) :
    ∃ trail ∈ sidePaths p.length,
      traversalEdges trail = (pathEdges p).image (Sym2.map (map F i right)) := by
  rcases he with ⟨hs,hf⟩ | ⟨hf,hs⟩
  · refine ⟨p.vertices.map (map F i right),?_,traversalEdges_map _ _⟩
    exact encode_oriented i left right hlt p.vertices p.consecutive p.nodup
      (by simpa [hs] using p.head_eq) (by simpa [hf] using p.last_eq)
  · refine ⟨p.vertices.reverse.map (map F i right),?_,?_⟩
    · simpa [BoundaryPath.length] using encode_oriented i left right hlt p.vertices.reverse
        (AKLT.listWalk_reverse (fun _ _ => sunAdj_symm) p.consecutive)
        (List.nodup_reverse.mpr p.nodup)
        (by simpa [hf] using p.last_eq) (by simpa [hs] using p.head_eq)
    · rw [traversalEdges_map,AKLT.traversalEdges_reverse]
      rfl

/-- Every canonical family with the same right leaf is bounded by R(n), for
all regional sizes and all lengths. Neither orientation nor side choice is
counted as part of the polymer. -/
theorem edge_family_card_le (F : Rectangle) (n : ℕ) (i : Fin 6) (right : ℤ)
    (S : Finset (Finset Edge))
    (hS : ∀ e ∈ S, ∃ p : BoundaryPath F 200,
      p.length=n ∧ pathEdges p=e ∧ ∃ left : ℤ, left < right ∧
      ((p.start = BoundaryLeaves.leaf F i left ∧ p.finish = BoundaryLeaves.leaf F i right) ∨
        (p.finish = BoundaryLeaves.leaf F i left ∧ p.start = BoundaryLeaves.leaf F i right))) :
    S.card ≤ sideCount n := by
  have hi := mapEdgeSets_injective F i right
  rw [sideCount_eq_card,← Finset.card_image_of_injective S hi]
  apply (Finset.card_le_card (t := (sidePaths n).image traversalEdges) ?_).trans Finset.card_image_le
  intro e he
  obtain ⟨edge,hedge,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨p,hp,rfl,left,hlt,hends⟩ := hS edge hedge
  obtain ⟨trail,ht,hrec⟩ := path_encoding p i left right hlt hends
  exact Finset.mem_image.mpr ⟨trail,by simpa only [hp] using ht,hrec⟩

end RegionalSide
end
end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.RegionalSide.edge_family_card_le
