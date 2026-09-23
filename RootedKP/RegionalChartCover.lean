import RootedKP.RegionalFaceChart
import Mathlib.Data.Finset.Card

/-!
Every radius-51 ambient neighborhood centered on the actual radius-200 sun
has an explicit corner-chart realization. The map preserves complete
adjacency stars (hence leaves), as well as core membership. There is no bound
on the rectangle dimensions and no assumed chart-coverage condition.
-/
namespace RootedKP.Honeycomb
set_option maxHeartbeats 0

/-- A convenient enclosing ball in the three graph-Lipschitz height coordinates. -/
def VertexWithin (u v : Vertex) (R : ℕ) : Prop :=
  heightQ v - heightQ u ≤ R ∧ heightQ u - heightQ v ≤ R ∧
  heightR v - heightR u ≤ R ∧ heightR u - heightR v ≤ R ∧
  heightS v - heightS u ≤ R ∧ heightS u - heightS v ≤ R

lemma VertexWithin.refl (u : Vertex) (R : ℕ) : VertexWithin u u R := by
  simp [VertexWithin]

lemma VertexWithin.symm {u v : Vertex} {R : ℕ} (h : VertexWithin u v R) :
    VertexWithin v u R := by unfold VertexWithin at *; omega

lemma VertexWithin.mono {u v : Vertex} {R T : ℕ} (h : VertexWithin u v R)
    (hRT : R ≤ T) : VertexWithin u v T := by unfold VertexWithin at *; omega

lemma VertexWithin.trans {u v w : Vertex} {R T : ℕ}
    (h : VertexWithin u v R) (h' : VertexWithin v w T) : VertexWithin u w (R+T) := by
  unfold VertexWithin at *
  push_cast
  omega

lemma VertexWithin.of_adj {u v : Vertex} (h : Adj u v) : VertexWithin u v 1 := by
  have hq := heightQ_lipschitz u v h
  have hr := heightR_lipschitz u v h
  have hs := heightS_lipschitz u v h
  exact ⟨hq.1,hq.2,hr.1,hr.2,hs.1,hs.2⟩

lemma Walk.vertexWithin {u v : Vertex} {n R : ℕ} (h : Walk u v n) (hn : n ≤ R) :
    VertexWithin u v R := by
  have hq := h.height_bounds heightQ_lipschitz
  have hr := h.height_bounds heightR_lipschitz
  have hs := h.height_bounds heightS_lipschitz
  unfold VertexWithin
  omega

lemma incident_dualWithin {u v : Vertex} {R : ℕ} {f g : Face}
    (hu : Incident u f) (hv : Incident v g) (h : VertexWithin u v R) :
    DualWithin f g (R+3) := by
  cases u <;> cases v <;>
    simp only [Incident] at hu hv <;>
    simp only [VertexWithin, heightQ, heightR, heightS] at h <;>
    rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    simp only [DualWithin, Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_ofNat] <;> omega

lemma DualWithin.mono {f g : Face} {L M : ℕ} (h : DualWithin f g L) (hLM : L ≤ M) :
    DualWithin f g M := by unfold DualWithin at *; omega

lemma sun_vertex_near_core {F : Rectangle} {s : ℕ} {u : Vertex} (hu : SunVertex F s u) :
    ∃ c, Core F s c ∧ VertexWithin u c 1 := by
  obtain ⟨v,hv⟩ := hu
  rcases hv.2 with hc | hc
  · exact ⟨u,hc,VertexWithin.refl u 1⟩
  · exact ⟨v,hc,VertexWithin.of_adj hv.1⟩

/-- A proved local model; the extra core radius ensures that entire stars at
radius R, including neighbors just outside the patch, are preserved. -/
structure RegionalChartCover (F : Rectangle) (u : Vertex) (R : ℕ) where
  iso : LatticeIso
  core_iff : ∀ v, VertexWithin u v (R+1) →
    (Core F 200 v ↔ BoundaryCharts.core .corner (iso.vertex v))

namespace RegionalChartCover

lemma adjacency_iff {F : Rectangle} {u : Vertex} {R : ℕ}
    (c : RegionalChartCover F u R) {v : Vertex} (hv : VertexWithin u v R) (w : Vertex) :
    SunAdj F 200 v w ↔ BoundaryCharts.Adj .corner (c.iso.vertex v) (c.iso.vertex w) := by
  by_cases ha : Adj v w
  · have hw := hv.trans (VertexWithin.of_adj ha)
    have hv' := hv.mono (Nat.le_succ R)
    simp only [SunAdj, BoundaryCharts.Adj, c.iso.adj_iff,
      c.core_iff v hv', c.core_iff w hw]
  · constructor
    · intro h; exact False.elim (ha h.1)
    · intro h; exact False.elim (ha ((c.iso.adj_iff v w).mp h.1))

lemma leaf_iff {F : Rectangle} {u : Vertex} {R : ℕ}
    (c : RegionalChartCover F u R) {v : Vertex} (hv : VertexWithin u v R) :
    Leaf F 200 v ↔ BoundaryCharts.Leaf .corner (c.iso.vertex v) := by
  constructor
  · rintro ⟨w,hw,hunique⟩
    have hn : BoundaryCharts.next .corner (c.iso.vertex v) = {c.iso.vertex w} := by
      ext z
      constructor
      · intro hz
        have hs : SunAdj F 200 v (c.iso.vertex.symm z) :=
          (c.adjacency_iff hv _).mpr (by simpa using (BoundaryCharts.mem_next _ _ _).mp hz)
        have he := hunique _ hs
        simp only [Finset.mem_singleton]
        exact (c.iso.vertex.apply_symm_apply z).symm.trans (congrArg c.iso.vertex he)
      · intro hz
        have he : z = c.iso.vertex w := Finset.mem_singleton.mp hz
        subst z
        exact (BoundaryCharts.mem_next _ _ _).mpr ((c.adjacency_iff hv w).mp hw)
    rw [BoundaryCharts.Leaf, hn]
    simp
  · intro hleaf
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hleaf
    refine ⟨c.iso.vertex.symm z, ?_, ?_⟩
    · apply (c.adjacency_iff hv _).mpr
      apply (BoundaryCharts.mem_next _ _ _).mp
      simp [hz]
    · intro w hw
      have hm := (BoundaryCharts.mem_next _ _ _).mpr ((c.adjacency_iff hv w).mp hw)
      rw [hz] at hm
      have he := Finset.mem_singleton.mp hm
      exact c.iso.vertex.injective (by simpa using he)

end RegionalChartCover

/-- Actual universal chart coverage, proved from the six halo inequalities. -/
theorem regional_chart_cover (F : Rectangle) (u : Vertex) (R : ℕ)
    (hu : SunVertex F 200 u) (hR : R ≤ 51) : Nonempty (RegionalChartCover F u R) := by
  obtain ⟨c,hc,huc⟩ := sun_vertex_near_core hu
  obtain ⟨f₀,hf₀,hinc⟩ := hc
  obtain ⟨e,he⟩ := radius200_face_chart F f₀ hf₀
  refine ⟨⟨e, ?_⟩⟩
  intro v hv
  have hcv : VertexWithin c v (R+2) := by
    convert huc.symm.trans hv using 1 <;> omega
  have hfoot : ∀ f, Incident v f → DualWithin f₀ f 56 := by
    intro f hf
    exact (incident_dualWithin hinc hf hcv).mono (by omega)
  rw [BoundaryCharts.core_iff]
  constructor
  · rintro ⟨f,hf,hi⟩
    exact ⟨e.face f, (he f (hfoot f hi)).mp hf, (e.incident_iff v f).mpr hi⟩
  · rintro ⟨f,hf,hi⟩
    let g := e.face.symm f
    have hgi : Incident v g := (e.incident_iff v g).mp (by simpa [g] using hi)
    exact ⟨g, (he g (hfoot g hgi)).mpr (by simpa [g] using hf), hgi⟩

/-- Radius26 suffices for short roots of length6 and intersecting paths through20. -/
theorem regional_chart_cover26 (F : Rectangle) (u : Vertex) (hu : SunVertex F 200 u) :
    Nonempty (RegionalChartCover F u 26) := regional_chart_cover F u 26 hu (by decide)

end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.regional_chart_cover26
#print axioms RootedKP.Honeycomb.RegionalChartCover.leaf_iff
