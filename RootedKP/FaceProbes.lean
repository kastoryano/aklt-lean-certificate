import RootedKP.FiniteRegion
import RootedKP.PolymerLength

namespace RootedKP.AKLT
open Honeycomb

/-- The literal six-edge boundary of an included face. -/
def faceLoop (F : Rectangle) (s : ℕ) (f : Face) (hf : FaceHalo F s f) : SimpleLoop F s := by
  rcases f with ⟨q, r⟩
  have hc : ∀ v ∈ faceVertices (q, r), Core F s v :=
    fun v hv => ⟨(q, r), hf, (mem_faceVertices (q, r) v).mp hv⟩
  have c₀ := hc (.a q r) (by simp [faceVertices])
  have c₁ := hc (.b (q - 1) r) (by simp [faceVertices])
  have c₂ := hc (.a (q - 1) r) (by simp [faceVertices])
  have c₃ := hc (.b (q - 1) (r - 1)) (by simp [faceVertices])
  have c₄ := hc (.a q (r - 1)) (by simp [faceVertices])
  have c₅ := hc (.b q (r - 1)) (by simp [faceVertices])
  exact {
    vertices := [.a q r, .b (q - 1) r, .a (q - 1) r,
      .b (q - 1) (r - 1), .a q (r - 1), .b q (r - 1)]
    start := .a q r
    finish := .b q (r - 1)
    head_eq := rfl
    last_eq := rfl
    nodup := by simp; omega
    consecutive := by simp [ListWalk, SunAdj, Adj, c₀, c₁, c₂, c₃, c₄, c₅]
    closing := by simp [SunAdj, Adj, c₀, c₅]
    nondegenerate := by simp
  }

def faceProbe (F : Rectangle) (f : Face) (hf : FaceHalo F haloRadius f) : Polymer F :=
  ⟨.loop, loopEdges (faceLoop F haloRadius f hf), ⟨faceLoop F haloRadius f hf, rfl⟩⟩

theorem faceProbe_length (F : Rectangle) (f : Face) (hf : FaceHalo F haloRadius f) :
    (faceProbe F f hf).length = 6 := by
  change (loopEdges (faceLoop F haloRadius f hf)).card = 6
  rw [loopEdges_card]
  cases f
  rfl

theorem faceProbe_contains_face {F : Rectangle} {f : Face}
    (hf : FaceHalo F haloRadius f) {u : Vertex} (hu : Incident u f) :
    u ∈ (faceProbe F f hf).support := by
  have hv := (mem_faceVertices f u).mpr hu
  cases f with
  | mk q r =>
      simp only [faceVertices, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [faceProbe, faceLoop, Polymer.support, loopEdges, traversalEdges,
          Sym2.toFinset_mk_eq]

/-- Every occupied regional edge admits one six-loop probe incompatible with
all polymers containing that edge. This statement assumes no KP estimate. -/
theorem face_probe_for_edge (F : Rectangle) (e : Edge)
    (he : ∃ p : Polymer F, e ∈ p.edges) :
    ∃ q : Polymer F, q.length = 6 ∧
      ∀ p : Polymer F, e ∈ p.edges → Polymer.Incompatible p q := by
  obtain ⟨p₀, hp₀⟩ := he
  have hsun := p₀.edges_subset F hp₀
  obtain ⟨u, hu, hneigh⟩ := Finset.mem_biUnion.mp hsun
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hneigh
  obtain ⟨f, hf, huf⟩ := (mem_coreSet F haloRadius u).mp hu
  refine ⟨faceProbe F f hf, faceProbe_length F f hf, ?_⟩
  intro p hp hd
  have hup : u ∈ p.support := Finset.mem_biUnion.mpr
    ⟨s(u, v), hp, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left u v)⟩
  exact Finset.disjoint_left.mp hd hup (faceProbe_contains_face hf huf)

end RootedKP.AKLT
