import RootedKP.RegionalChartCover
import RootedKP.PathConfinement

namespace RootedKP.Honeycomb
set_option maxHeartbeats 0

/-- Any two vertices of a literal traversal lie within its edge length. -/
theorem listWalk_vertexWithin {vs : List Vertex} (hw : ListWalk Adj vs)
    {u v : Vertex} (hu : u ∈ vs) (hv : v ∈ vs) :
    VertexWithin u v (vs.length-1) := by
  obtain ⟨i,hi,hui⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j,hj,hvj⟩ := List.mem_iff_getElem.mp hv
  let vertex : ℕ → Vertex := fun k => vs.getD k (.a 0 0)
  have hstep : ∀ k < vs.length-1, Adj (vertex k) (vertex (k+1)) := by
    intro k hk
    exact listWalk_getD hw (by omega) _
  have hui' : vertex i = u := by simpa only [vertex, List.getD_eq_getElem _ _ hi] using hui
  have hvj' : vertex j = v := by simpa only [vertex, List.getD_eq_getElem _ _ hj] using hvj
  by_cases hij : i ≤ j
  · have hh := indexed_subwalk hstep i (j-i) (by omega)
    have heq : i+(j-i) = j := by omega
    rw [heq,hui',hvj'] at hh
    exact hh.vertexWithin (by omega)
  · have hh := indexed_subwalk hstep j (i-j) (by omega)
    have heq : j+(i-j) = i := by omega
    rw [heq,hui',hvj'] at hh
    exact (hh.vertexWithin (by omega)).symm

lemma listWalk_ambient {F : Rectangle} {s : ℕ} {vs : List Vertex}
    (hw : ListWalk (SunAdj F s) vs) : ListWalk Adj vs := by
  induction vs with
  | nil => trivial
  | cons a tail ih =>
    cases tail with
    | nil => trivial
    | cons b rest => exact ⟨hw.1.1,ih hw.2⟩

/-- Intersecting traversals fit in the sum of their edge-length radii around
any chosen vertex of the first traversal. -/
theorem intersecting_walks_vertexWithin {root path : List Vertex}
    (hr : ListWalk Adj root) (hp : ListWalk Adj path)
    {center joint v : Vertex} (hc : center ∈ root) (hj : joint ∈ root)
    (hj' : joint ∈ path) (hv : v ∈ path) :
    VertexWithin center v ((root.length-1)+(path.length-1)) :=
  (listWalk_vertexWithin hr hc hj).trans (listWalk_vertexWithin hp hj' hv)

namespace RegionalChartCover

/-- One common chart isometry preserves a complete bounded regional traversal. -/
theorem listWalk_map {F : Rectangle} {center : Vertex} {R : ℕ}
    (c : RegionalChartCover F center R) {vs : List Vertex}
    (hw : ListWalk (SunAdj F 200) vs)
    (hb : ∀ v ∈ vs, VertexWithin center v R) :
    ListWalk (BoundaryCharts.Adj .corner) (vs.map c.iso.vertex) := by
  induction vs with
  | nil => trivial
  | cons u tail ih =>
    cases tail with
    | nil => trivial
    | cons v rest =>
      exact ⟨(c.adjacency_iff (hb u (by simp)) v).mp hw.1,
        ih hw.2 (fun w hw => hb w (List.mem_cons_of_mem u hw))⟩

/-- The advertised radius26 handles a short root and every intersecting path
of length at most20, using the SAME map for the whole family. -/
theorem short_intersecting_path_map {F : Rectangle} {center : Vertex}
    (c : RegionalChartCover F center 26) {root path : List Vertex}
    (hr : ListWalk (SunAdj F 200) root) (hp : ListWalk (SunAdj F 200) path)
    (hlr : root.length-1 ≤ 6) (hlp : path.length-1 ≤ 20)
    (hc : center ∈ root) (hinter : ∃ joint, joint ∈ root ∧ joint ∈ path) :
    ListWalk (BoundaryCharts.Adj .corner) (path.map c.iso.vertex) ∧
      (∀ v ∈ path, Leaf F 200 v ↔ BoundaryCharts.Leaf .corner (c.iso.vertex v)) ∧
      (path.Nodup → (path.map c.iso.vertex).Nodup) := by
  obtain ⟨joint,hj,hj'⟩ := hinter
  have hb : ∀ v ∈ path, VertexWithin center v 26 := by
    intro v hv
    exact (intersecting_walks_vertexWithin (listWalk_ambient hr) (listWalk_ambient hp)
      hc hj hj' hv).mono (by omega)
  exact ⟨c.listWalk_map hp hb, fun v hv => c.leaf_iff (hb v hv),
    fun hn => hn.map c.iso.vertex.injective⟩

end RegionalChartCover
end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.RegionalChartCover.short_intersecting_path_map
