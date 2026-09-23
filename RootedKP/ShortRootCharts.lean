import RootedKP.BoundaryFastCounts
import RootedKP.BoundaryChartLeaves

/-!
Complete local searches for boundary paths intersecting a specified root.
The finite start window is justified from the graph metric below; it is not
an experimental cutoff. Traversals use a fixed order of their leaf endpoints.
-/

namespace RootedKP.ShortRootCharts

open Honeycomb BoundaryCharts Enumeration LoopCounts BoundaryCounts

set_option maxHeartbeats 0

/-- Every visited vertex lies within the number of steps of the initial
height interval. The statement applies to all three honeycomb heights. -/
theorem extends_height_interval (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) {n : ℕ} {trail result : List Vertex}
    (he : Extends (next C) n trail result) (origin : ℤ) (b : ℕ)
    (hb : ∀ v ∈ trail, height v - origin ≤ b ∧ origin - height v ≤ b) :
    ∀ v ∈ result, height v - origin ≤ (b + n : ℕ) ∧
      origin - height v ≤ (b + n : ℕ) := by
  induction he generalizing b with
  | refl trail => simpa using hb
  | @step u w us result n hw hnew he ih =>
    have hadj : Honeycomb.Adj u w := (mem_next C u w).mp hw |>.1
    have hstep := lip u w hadj
    have hu := hb u (by simp)
    have hnewbound : ∀ v ∈ w :: u :: us,
        height v - origin ≤ (b + 1 : ℕ) ∧ origin - height v ≤ (b + 1 : ℕ) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · constructor <;> omega
      · have := hb v hv
        constructor <;> omega
    have hi := ih (b + 1) hnewbound
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem extends_member_height (C : Chart) (height : Vertex → ℤ)
    (lip : OneLipschitz height) {n : ℕ} {start : Vertex} {trail : List Vertex}
    (he : Extends (next C) n [start] trail) {v : Vertex} (hv : v ∈ trail) :
    height v - height start ≤ n ∧ height start - height v ≤ n := by
  simpa using extends_height_interval C height lip he (height start) 0
    (by
      intro w hw
      have hw' : w = start := by simpa using hw
      subst w
      simp) v hv

/-- The sole length-three path at a convex corner, including its two leaves. -/
def cornerRootThree : Finset Vertex :=
  {.a (-1) 1, .b (-1) 0, .a (-1) 0, .b (-2) 0}

def hitsRoot (root : Finset Vertex) (trail : List Vertex) : Prop :=
  ∃ v ∈ root, v ∈ trail

instance (root : Finset Vertex) (trail : List Vertex) :
    Decidable (hitsRoot root trail) := by
  unfold hitsRoot
  infer_instance

/-- Order the two corner rays consecutively, and each ray away from the corner.
Only its restriction to actual leaves is used. -/
def leafBefore : Vertex → Vertex → Prop
  | .a q r, .a q' r' => q < q'
  | .a _ _, .b _ _ => True
  | .b _ _, .a _ _ => False
  | .b q r, .b q' r' => r' < r

instance (u v : Vertex) : Decidable (leafBefore u v) := by
  cases u <;> cases v <;> unfold leafBefore <;> infer_instance

def accepts (root : Finset Vertex) (start : Vertex) (trail : List Vertex) : Prop :=
  endsAt (fun finish => leafCode .corner finish ∧ leafBefore start finish) trail ∧
  hitsRoot root trail

instance (root : Finset Vertex) (start : Vertex) (trail : List Vertex) :
    Decidable (accepts root start trail) := by
  unfold accepts
  infer_instance

/-- Independent specification on the infinite corner chart. -/
def Traversal (root : Finset Vertex) (n : ℕ) (trail : List Vertex) : Prop :=
  ∃ start, Leaf .corner start ∧ Extends (next .corner) n [start] trail ∧
    accepts root start trail

def starts (n : ℕ) : Finset Vertex :=
  ((Finset.range ((n + 1) / 2 + 1)).image (fun (k : ℕ) => Vertex.a ((k : ℤ) - 1) 1)) ∪
  ((Finset.range ((n + 1) / 2 + 1)).image (fun (k : ℕ) => Vertex.b (-2) (-(k : ℤ))))

theorem root_three_start_bound {n : ℕ} {start : Vertex} {trail : List Vertex}
    (hs : Leaf .corner start) (he : Extends (next .corner) n [start] trail)
    (hit : hitsRoot cornerRootThree trail) : start ∈ starts n := by
  obtain ⟨v, hv, hvt⟩ := hit
  have hq := extends_member_height .corner heightQ heightQ_lipschitz he hvt
  have hr := extends_member_height .corner heightR heightR_lipschitz he hvt
  have hs' := (leafCode_iff .corner start).mpr hs
  change upperLeaf start ∨ leftLeaf start at hs'
  have vq : heightQ v ≤ -1 := by
    simp only [cornerRootThree, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  have vr : 0 ≤ heightR v := by
    simp only [cornerRootThree, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> decide
  unfold starts
  rcases hs' with hu | hl
  · cases start with
    | b q r => exact False.elim hu
    | a q r =>
      obtain ⟨hq0, rfl⟩ := hu
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(q + 1).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        simp only [heightQ] at hq vq
        have heq := Int.toNat_of_nonneg (show 0 ≤ q + 1 by omega)
        omega
      · have heq := Int.toNat_of_nonneg (show 0 ≤ q + 1 by omega)
        congr 1
        omega
  · cases start with
    | a q r => exact False.elim hl
    | b q r =>
      obtain ⟨rfl, hr0⟩ := hl
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(-r).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        simp only [heightR] at hr vr
        have heq := Int.toNat_of_nonneg (show 0 ≤ -r by omega)
        omega
      · have heq := Int.toNat_of_nonneg (show 0 ≤ -r by omega)
        congr 1
        omega

def pathsFrom (root : Finset Vertex) (n : ℕ) (start : Vertex) : Finset (List Vertex) :=
  (extensions (next .corner) n [start]).filter (accepts root start)

def paths (root : Finset Vertex) (n : ℕ) : Finset (List Vertex) :=
  (starts n).biUnion (pathsFrom root n)

theorem starts_are_leaves {n : ℕ} {v : Vertex} (hv : v ∈ starts n) :
    Leaf .corner v := by
  rw [starts, Finset.mem_union] at hv
  rcases hv with hv | hv
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    apply upperLeaf_is_leaf
    exact ⟨by omega, rfl⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    apply leftLeaf_is_leaf
    exact ⟨rfl, by omega⟩

theorem mem_paths_three_iff (n : ℕ) (trail : List Vertex) :
    trail ∈ paths cornerRootThree n ↔ Traversal cornerRootThree n trail := by
  simp only [paths, pathsFrom, Finset.mem_biUnion, Finset.mem_filter, mem_extensions_iff]
  constructor
  · rintro ⟨start, hs, he, ha⟩
    exact ⟨start, starts_are_leaves hs, he, ha⟩
  · rintro ⟨start, hs, he, ha⟩
    exact ⟨start, root_three_start_bound hs he ha.2, he, ha⟩

def count (root : Finset Vertex) (n : ℕ) : ℕ :=
  ∑ start ∈ starts n, fastCount .corner (accepts root start) n [start]

theorem count_eq_card (root : Finset Vertex) (n : ℕ) :
    count root n = (paths root n).card := by
  unfold count paths
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro start _
    rw [BoundaryCounts.fastCount_eq, acceptedCount_eq_card]
    rfl
  · intro u hu v hv hne
    apply Finset.disjoint_left.mpr
    intro trail htu htv
    have heu := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp htu).1
    have hev := (mem_extensions_iff _ _ _ _).mp (Finset.mem_filter.mp htv).1
    have : [u] = [v] := (extends_drop heu).symm.trans (extends_drop hev)
    exact hne (List.cons.inj this).1

end RootedKP.ShortRootCharts
