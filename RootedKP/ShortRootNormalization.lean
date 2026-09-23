import RootedKP.ShortRootCharts
import RootedKP.BoundaryPrefixBounds
import RootedKP.HoneycombSymmetry

/-!
# Finite local representatives for arbitrary corner-chart roots

A translation clamps an anchor's q-coordinate at16 and its r-coordinate at−16.
It preserves the exact corner graph throughout coordinate radius14. A root of
length≤6 together with an intersecting path of length≤20 fits in this patch,
by the graph-Lipschitz height bounds. Far-side and bulk roots are therefore
included, rather than silently assumed to lie near the corner.
-/
namespace RootedKP.ShortRootRepresentatives
open Honeycomb BoundaryCharts BoundaryCounts Enumeration LoopCounts ShortRootCharts

set_option maxHeartbeats 0

def InPatch (anchor v : Vertex) : Prop :=
  qCoord v - qCoord anchor ≤ 14 ∧ qCoord anchor - qCoord v ≤ 14 ∧
  rCoord v - rCoord anchor ≤ 14 ∧ rCoord anchor - rCoord v ≤ 14

def normalize (anchor : Vertex) : Vertex → Vertex :=
  translate (min (qCoord anchor) 16 - qCoord anchor)
    (max (rCoord anchor) (-16) - rCoord anchor)

theorem normalize_injective (anchor : Vertex) : Function.Injective (normalize anchor) :=
  translate_injective _ _

theorem normalize_core_iff {anchor v : Vertex} (hv : InPatch anchor v) :
    core .corner (normalize anchor v) ↔ core .corner v := by
  cases anchor <;> cases v <;>
    simp only [normalize, translate, core, qCoord, rCoord, InPatch] at *
  all_goals simp only [min_def, max_def]; split_ifs <;> omega

theorem translate_adj_iff (dq dr : ℤ) (u v : Vertex) :
    Honeycomb.Adj (translate dq dr u) (translate dq dr v) ↔ Honeycomb.Adj u v := by
  cases u <;> cases v <;> simp only [translate, Honeycomb.Adj] <;> omega

theorem normalize_adj_iff {anchor u v : Vertex} (hu : InPatch anchor u)
    (hv : InPatch anchor v) :
    BoundaryCharts.Adj .corner (normalize anchor u) (normalize anchor v) ↔
      BoundaryCharts.Adj .corner u v := by
  simp only [BoundaryCharts.Adj, normalize_core_iff hu, normalize_core_iff hv]
  exact and_congr_left (fun _ => translate_adj_iff _ _ u v)

theorem normalize_leaf_iff {anchor v : Vertex} (hv : InPatch anchor v) :
    Leaf .corner (normalize anchor v) ↔ Leaf .corner v := by
  rw [← leafCode_iff, ← leafCode_iff]
  cases anchor <;> cases v <;>
    simp only [normalize, translate, leafCode, upperLeaf, leftLeaf,
      qCoord, rCoord, InPatch] at *
  all_goals simp only [min_def, max_def, false_or, or_false]; split_ifs <;> omega

theorem anchor_in_patch (anchor : Vertex) : InPatch anchor anchor := by
  simp [InPatch]

/-- Height radius27 is sufficient for coordinate radius14, for both phases. -/
theorem inPatch_of_height_bounds {anchor v : Vertex}
    (hq : heightQ v - heightQ anchor ≤ 27 ∧ heightQ anchor - heightQ v ≤ 27)
    (hr : heightR v - heightR anchor ≤ 27 ∧ heightR anchor - heightR v ≤ 27) :
    InPatch anchor v := by
  cases anchor <;> cases v <;> simp only [heightQ, heightR, qCoord, rCoord, InPatch] at * <;> omega

theorem extends_in_patch {n : ℕ} (hn : n ≤ 27) {start : Vertex} {trail : List Vertex}
    (he : Extends (next .corner) n [start] trail) : ∀ v ∈ trail, InPatch start v := by
  intro v hv
  have hq := extends_member_height .corner heightQ heightQ_lipschitz he hv
  have hr := extends_member_height .corner heightR heightR_lipschitz he hv
  apply inPatch_of_height_bounds <;> constructor <;> omega


/-- Any two vertices of an extended traversal have height separation bounded
by the number of new steps plus the initial traversal diameter. -/
theorem extends_height_diameter (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) {n : ℕ} {initial result : List Vertex}
    (he : Extends (next C) n initial result) (b : ℕ)
    (hd : ∀ x ∈ initial, ∀ y ∈ initial,
      height x - height y ≤ b ∧ height y - height x ≤ b) :
    ∀ x ∈ result, ∀ y ∈ result,
      height x - height y ≤ (b + n : ℕ) ∧ height y - height x ≤ (b + n : ℕ) := by
  induction he generalizing b with
  | refl initial => simpa using hd
  | @step u v us result n hv _ he ih =>
    have hs := lip u v ((mem_next C u v).mp hv).1
    have hnew : ∀ x ∈ v :: u :: us, ∀ y ∈ v :: u :: us,
        height x - height y ≤ (b + 1 : ℕ) ∧ height y - height x ≤ (b + 1 : ℕ) := by
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_cons.mp hy with rfl | hy
        · constructor <;> omega
        · have hu := hd u (by simp) y hy
          constructor <;> omega
      · rcases List.mem_cons.mp hy with hy | hy
        · have hu := hd x hx u (by simp)
          subst y
          constructor <;> omega
        · have hh := hd x hx y hy
          constructor <;> omega
    have hh := ih (b + 1) hnew
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem extends_pair_height (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) {n : ℕ} {start : Vertex} {trail : List Vertex}
    (he : Extends (next C) n [start] trail) {x y : Vertex} (hx : x ∈ trail) (hy : y ∈ trail) :
    height x - height y ≤ n ∧ height y - height x ≤ n := by
  have hd : ∀ a ∈ [start], ∀ b ∈ [start],
      height a - height b ≤ (0 : ℕ) ∧ height b - height a ≤ (0 : ℕ) := by
    intro a ha b hb
    simp only [List.mem_singleton] at ha hb
    subst a
    subst b
    simp
  simpa using extends_height_diameter C height lip he 0 hd x hx y hy

/-- A path meeting a short root lies in the SAME patch anchored at the root. -/
theorem intersecting_in_patch {ell n : ℕ} (hell : ell ≤ 6) (hn : n ≤ 20)
    {anchor start x : Vertex} {root trail : List Vertex}
    (hroot : Extends (next .corner) ell [anchor] root)
    (he : Extends (next .corner) n [start] trail) (hx : x ∈ root) (hxt : x ∈ trail) :
    ∀ v ∈ trail, InPatch anchor v := by
  intro v hv
  have rootQ := extends_member_height .corner heightQ heightQ_lipschitz hroot hx
  have rootR := extends_member_height .corner heightR heightR_lipschitz hroot hx
  have trailQ := extends_pair_height .corner heightQ heightQ_lipschitz he hv hxt
  have trailR := extends_pair_height .corner heightR heightR_lipschitz he hv hxt
  apply inPatch_of_height_bounds <;> constructor <;> omega

/-- Local graph preservation on the completed traversal suffices for transport. -/
theorem extends_map_local {C D : Chart} (f : Vertex → Vertex)
    (hinj : Function.Injective f) {n : ℕ} {initial result : List Vertex}
    (he : Extends (next C) n initial result)
    (hstep : ∀ u ∈ result, ∀ v ∈ result, BoundaryCharts.Adj C u v →
      BoundaryCharts.Adj D (f u) (f v)) :
    Extends (next D) n (initial.map f) (result.map f) := by
  induction he with
  | refl initial => exact .refl _
  | @step u v us result n hv hnew he ih =>
    have hmem : ∀ w ∈ v :: u :: us, w ∈ result := by
      intro w hw
      apply List.mem_of_mem_drop (i := n)
      simpa [extends_drop he] using hw
    apply Extends.step ((mem_next D _ _).mpr
      (hstep u (hmem _ (by simp)) v (hmem _ (by simp)) ((mem_next C u v).mp hv)))
    · intro hm
      change f v ∈ (u :: us).map f at hm
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hm
      exact hnew ((hinj heq) ▸ hw)
    · exact ih hstep

theorem normalize_extends {n : ℕ} {anchor : Vertex} {initial result : List Vertex}
    (he : Extends (next .corner) n initial result)
    (hp : ∀ v ∈ result, InPatch anchor v) :
    Extends (next .corner) n (initial.map (normalize anchor)) (result.map (normalize anchor)) := by
  apply extends_map_local _ (normalize_injective anchor) he
  intro u hu v hv hadj
  exact (normalize_adj_iff (hp u hu) (hp v hv)).mpr hadj

theorem normalize_leafBefore (anchor u v : Vertex) :
    leafBefore (normalize anchor u) (normalize anchor v) ↔ leafBefore u v := by
  cases u <;> cases v <;> simp [leafBefore, normalize, translate]

/-- Every short boundary root is transported exactly, including leaf endpoints. -/
theorem normalize_boundary_root {n : ℕ} (hn : n ≤ 6) {anchor : Vertex}
    {trail : List Vertex} (he : Extends (next .corner) n [anchor] trail)
    (hs : Leaf .corner anchor) (ht : endsAt (Leaf .corner) trail) :
    Extends (next .corner) n [normalize anchor anchor] (trail.map (normalize anchor)) ∧
      Leaf .corner (normalize anchor anchor) ∧
      endsAt (Leaf .corner) (trail.map (normalize anchor)) := by
  have hp := extends_in_patch (by omega : n ≤ 27) he
  refine ⟨by simpa using normalize_extends he hp,
    (normalize_leaf_iff (anchor_in_patch anchor)).mpr hs, ?_⟩
  cases trail with
  | nil => exact ht
  | cons v vs => exact (normalize_leaf_iff (hp v (by simp))).mpr ht

/-- All intersecting paths of length≤20 transport into the SAME normalized root.
The fixed endpoint orientation is preserved, so this gives an injection on the
traversals counted by the short-root counter. -/
theorem normalize_intersecting_traversal {ell n : ℕ} (hell : ell ≤ 6) (hn : n ≤ 20)
    {anchor : Vertex} {root trail : List Vertex}
    (hroot : Extends (next .corner) ell [anchor] root)
    (ht : Traversal root.toFinset n trail) :
    Traversal (root.map (normalize anchor)).toFinset n (trail.map (normalize anchor)) := by
  obtain ⟨start, hs, he, hend, x, hxr, hxt⟩ := ht
  have hx : x ∈ root := List.mem_toFinset.mp hxr
  have hp := intersecting_in_patch hell hn hroot he hx hxt
  have hstart : start ∈ trail := by
    apply List.mem_of_mem_drop (i := n)
    simp [extends_drop he]
  refine ⟨normalize anchor start, (normalize_leaf_iff (hp start hstart)).mpr hs,
    by simpa using normalize_extends he hp, ?_, ?_⟩
  · cases trail with
    | nil => exact hend
    | cons finish rest =>
      change leafCode .corner finish ∧ leafBefore start finish at hend
      change leafCode .corner (normalize anchor finish) ∧
        leafBefore (normalize anchor start) (normalize anchor finish)
      refine ⟨?_, (normalize_leafBefore _ _ _).mpr hend.2⟩
      rw [leafCode_iff] at hend ⊢
      exact (normalize_leaf_iff (hp finish (by simp))).mpr hend.1
  · refine ⟨normalize anchor x, ?_, List.mem_map.mpr ⟨x, hxt, rfl⟩⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)

end RootedKP.ShortRootRepresentatives
