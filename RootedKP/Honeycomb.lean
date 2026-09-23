import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
Exact integer-coordinate honeycomb graph used in Appendix A.2.
These definitions describe the infinite ambient graph and the paper's suns;
there is no enumeration cutoff or hypothesis asserting a geometric bound.
-/
namespace RootedKP.Honeycomb

inductive Vertex where
  | a (q r : ℤ)
  | b (q r : ℤ)
  deriving DecidableEq, Repr

abbrev Face := ℤ × ℤ

def Adj : Vertex → Vertex → Prop
  | .a q r, .b q' r' =>
      (q' = q ∧ r' = r) ∨ (q' = q - 1 ∧ r' = r) ∨ (q' = q ∧ r' = r - 1)
  | .b q' r', .a q r =>
      (q' = q ∧ r' = r) ∨ (q' = q - 1 ∧ r' = r) ∨ (q' = q ∧ r' = r - 1)
  | _, _ => False

instance (u v : Vertex) : Decidable (Adj u v) := by
  cases u <;> cases v <;> unfold Adj <;> infer_instance

theorem adj_symm {u v : Vertex} (h : Adj u v) : Adj v u := by
  cases u <;> cases v <;> simpa only [Adj] using h

theorem adj_irrefl (v : Vertex) : ¬ Adj v v := by
  cases v <;> simp [Adj]

/-- The three ambient neighbors, with no search radius or bounded box. -/
def neighbors : Vertex → Finset Vertex
  | .a q r => {.b q r, .b (q - 1) r, .b q (r - 1)}
  | .b q r => {.a q r, .a (q + 1) r, .a q (r + 1)}

@[simp] theorem mem_neighbors (u v : Vertex) : v ∈ neighbors u ↔ Adj u v := by
  cases u <;> cases v <;> simp [neighbors, Adj] <;> omega

@[simp] theorem neighbors_card (v : Vertex) : (neighbors v).card = 3 := by
  cases v with
  | a q r =>
      have hq : q ≠ q - 1 := by omega
      have hr : r ≠ r - 1 := by omega
      simp [neighbors, hq, hr]
  | b q r =>
      have hq : q ≠ q + 1 := by omega
      have hr : r ≠ r + 1 := by omega
      simp [neighbors, hq, hr]

def heightQ : Vertex → ℤ
  | .a q _ => 2 * q
  | .b q _ => 2 * q + 1

def heightR : Vertex → ℤ
  | .a _ r => 2 * r
  | .b _ r => 2 * r + 1

def heightS : Vertex → ℤ
  | .a q r => 2 * (q + r)
  | .b q r => 2 * (q + r) + 1

def OneLipschitz (h : Vertex → ℤ) : Prop :=
  ∀ u v, Adj u v → h v - h u ≤ 1 ∧ h u - h v ≤ 1

theorem heightQ_lipschitz : OneLipschitz heightQ := by
  intro u v h
  cases u <;> cases v <;> simp_all [Adj, heightQ] <;> omega

theorem heightR_lipschitz : OneLipschitz heightR := by
  intro u v h
  cases u <;> cases v <;> simp_all [Adj, heightR] <;> omega

theorem heightS_lipschitz : OneLipschitz heightS := by
  intro u v h
  cases u <;> cases v <;> simp_all [Adj, heightS] <;> omega

/-- Rotation through sixty degrees about face `(0,0)`. -/
def rotate : Vertex → Vertex
  | .a q r => .b (-r - 1) (q + r)
  | .b q r => .a (-r - 1) (q + r + 1)

theorem rotate_adj {u v : Vertex} (h : Adj u v) : Adj (rotate u) (rotate v) := by
  cases u <;> cases v <;> simp_all [Adj, rotate] <;> omega

theorem rotate_six (v : Vertex) :
    rotate (rotate (rotate (rotate (rotate (rotate v))))) = v := by
  cases v <;> simp [rotate] <;> congr 1 <;> omega

/-- A walk with its exact number of edges. It need not be simple. -/
inductive Walk : Vertex → Vertex → ℕ → Prop where
  | nil (v : Vertex) : Walk v v 0
  | cons {u v w : Vertex} {n : ℕ} : Adj u v → Walk v w n → Walk u w (n + 1)

theorem Walk.height_bounds {u v : Vertex} {n : ℕ} {h : Vertex → ℤ}
    (lip : OneLipschitz h) (walk : Walk u v n) :
    h v - h u ≤ (n : ℤ) ∧ h u - h v ≤ (n : ℤ) := by
  induction walk with
  | nil v => simp
  | @cons u v w n huv hvw ih =>
      have huv' := lip u v huv
      constructor <;> omega

/-- The three faces incident to a primal vertex. -/
def Incident : Vertex → Face → Prop
  | .a q r, f => f = (q, r) ∨ f = (q + 1, r) ∨ f = (q, r + 1)
  | .b q r, f => f = (q + 1, r) ∨ f = (q, r + 1) ∨ f = (q + 1, r + 1)

structure Rectangle where
  qmin : ℤ
  qmax : ℤ
  rmin : ℤ
  rmax : ℤ
  q_order : qmin ≤ qmax
  r_order : rmin ≤ rmax

/-- The six exact coordinate inequalities for `D_s(F)`. -/
def FaceHalo (F : Rectangle) (s : ℕ) (f : Face) : Prop :=
  F.qmin - s ≤ f.1 ∧ f.1 ≤ F.qmax + s ∧
  F.rmin - s ≤ f.2 ∧ f.2 ≤ F.rmax + s ∧
  F.qmin + F.rmin - s ≤ f.1 + f.2 ∧ f.1 + f.2 ≤ F.qmax + F.rmax + s

def Core (F : Rectangle) (s : ℕ) (v : Vertex) : Prop :=
  ∃ f, FaceHalo F s f ∧ Incident v f

/-- An edge belongs to the sun precisely when it touches a core. -/
def SunAdj (F : Rectangle) (s : ℕ) (u v : Vertex) : Prop :=
  Adj u v ∧ (Core F s u ∨ Core F s v)

def SunVertex (F : Rectangle) (s : ℕ) (v : Vertex) : Prop :=
  ∃ w, SunAdj F s v w

def Leaf (F : Rectangle) (s : ℕ) (v : Vertex) : Prop :=
  ∃! w, SunAdj F s v w

theorem sunAdj_symm {F : Rectangle} {s : ℕ} {u v : Vertex}
    (h : SunAdj F s u v) : SunAdj F s v u :=
  ⟨adj_symm h.1, h.2.symm⟩

theorem core_heightQ_upper {F : Rectangle} {s : ℕ} {v : Vertex}
    (h : Core F s v) : heightQ v ≤ 2 * (F.qmax + s) + 1 := by
  obtain ⟨⟨q, r⟩, hf, hi⟩ := h
  have hq := hf.2.1
  cases v <;> simp_all [Incident, heightQ] <;> omega

theorem sun_heightQ_upper {F : Rectangle} {s : ℕ} {v : Vertex}
    (h : SunVertex F s v) : heightQ v ≤ 2 * (F.qmax + s) + 2 := by
  obtain ⟨w, hw⟩ := h
  rcases hw.2 with hv | hwcore
  · have := core_heightQ_upper hv
    omega
  · have hc := core_heightQ_upper hwcore
    have hl := heightQ_lipschitz v w hw.1
    omega

theorem core_a_iff_faces (F : Rectangle) (s : ℕ) (q r : ℤ) :
    Core F s (.a q r) ↔
      FaceHalo F s (q, r) ∨ FaceHalo F s (q + 1, r) ∨ FaceHalo F s (q, r + 1) := by
  simp [Core, Incident, and_or_left, exists_or]

theorem core_b_iff_faces (F : Rectangle) (s : ℕ) (q r : ℤ) :
    Core F s (.b q r) ↔
      FaceHalo F s (q + 1, r) ∨ FaceHalo F s (q, r + 1) ∨
        FaceHalo F s (q + 1, r + 1) := by
  simp [Core, Incident, and_or_left, exists_or]

/-- Exact core membership on the `a` sublattice, for every rectangle and halo. -/
theorem core_a_coordinates (F : Rectangle) (s : ℕ) (q r : ℤ) :
    Core F s (.a q r) ↔
      F.qmin - s - 1 ≤ q ∧ q ≤ F.qmax + s ∧
      F.rmin - s - 1 ≤ r ∧ r ≤ F.rmax + s ∧
      F.qmin + F.rmin - s - 1 ≤ q + r ∧ q + r ≤ F.qmax + F.rmax + s := by
  rw [core_a_iff_faces]
  have hq := F.q_order
  have hr := F.r_order
  simp only [FaceHalo, Prod.fst, Prod.snd]
  omega

/-- Exact core membership on the `b` sublattice, including the corner phase. -/
theorem core_b_coordinates (F : Rectangle) (s : ℕ) (q r : ℤ) :
    Core F s (.b q r) ↔
      F.qmin - s - 1 ≤ q ∧ q ≤ F.qmax + s ∧
      F.rmin - s - 1 ≤ r ∧ r ≤ F.rmax + s ∧
      F.qmin + F.rmin - s - 2 ≤ q + r ∧ q + r ≤ F.qmax + F.rmax + s - 1 := by
  rw [core_b_iff_faces]
  have hq := F.q_order
  have hr := F.r_order
  simp only [FaceHalo, Prod.fst, Prod.snd]
  omega

/-- A noncore has at most one core neighbor. This proves the sun has no
extra degree-two vertices for arbitrary rectangle dimensions. -/
theorem noncore_core_neighbor_unique {F : Rectangle} {s : ℕ} {v u w : Vertex}
    (hv : ¬ Core F s v) (hu : Core F s u) (hw : Core F s w)
    (hvu : Adj v u) (hvw : Adj v w) : u = w := by
  have hq := F.q_order
  have hr := F.r_order
  cases v <;> cases u <;> cases w <;>
    simp_all only [Adj, core_a_coordinates, core_b_coordinates,
      Vertex.a.injEq, Vertex.b.injEq] <;> omega

/-- At a core, at most one neighbor is a noncore. Thus distinct leaves
cannot have a common attachment core. -/
theorem core_noncore_neighbor_unique {F : Rectangle} {s : ℕ} {v u w : Vertex}
    (hv : Core F s v) (hu : ¬ Core F s u) (hw : ¬ Core F s w)
    (hvu : Adj v u) (hvw : Adj v w) : u = w := by
  have hq := F.q_order
  have hr := F.r_order
  cases v <;> cases u <;> cases w <;>
    simp_all only [Adj, core_a_coordinates, core_b_coordinates,
      Vertex.a.injEq, Vertex.b.injEq] <;> omega

theorem noncore_sun_vertex_is_leaf {F : Rectangle} {s : ℕ} {v : Vertex}
    (hv : SunVertex F s v) (hc : ¬ Core F s v) : Leaf F s v := by
  obtain ⟨w, hw⟩ := hv
  have hwcore : Core F s w := hw.2.resolve_left hc
  refine ⟨w, hw, ?_⟩
  intro u hu
  exact noncore_core_neighbor_unique hc (hu.2.resolve_left hc) hwcore hu.1 hw.1

theorem sun_vertex_core_or_leaf {F : Rectangle} {s : ℕ} {v : Vertex}
    (h : SunVertex F s v) : Core F s v ∨ Leaf F s v := by
  by_cases hc : Core F s v
  · exact Or.inl hc
  · exact Or.inr (noncore_sun_vertex_is_leaf h hc)

theorem core_not_leaf {F : Rectangle} {s : ℕ} {v : Vertex}
    (hv : Core F s v) : ¬ Leaf F s v := by
  intro h
  obtain ⟨w, hw, unique⟩ := h
  cases v with
  | a q r =>
      have h₀ : SunAdj F s (.a q r) (.b q r) :=
        ⟨by simp [Adj], Or.inl hv⟩
      have h₁ : SunAdj F s (.a q r) (.b (q - 1) r) :=
        ⟨by simp [Adj], Or.inl hv⟩
      have heq := (unique _ h₀).trans (unique _ h₁).symm
      simp only [Vertex.b.injEq] at heq
      omega
  | b q r =>
      have h₀ : SunAdj F s (.b q r) (.a q r) :=
        ⟨by simp [Adj], Or.inl hv⟩
      have h₁ : SunAdj F s (.b q r) (.a (q + 1) r) :=
        ⟨by simp [Adj], Or.inl hv⟩
      have heq := (unique _ h₀).trans (unique _ h₁).symm
      simp only [Vertex.a.injEq] at heq
      omega

theorem leaf_not_core {F : Rectangle} {s : ℕ} {v : Vertex}
    (h : Leaf F s v) : ¬ Core F s v := fun hc => core_not_leaf hc h

theorem leaf_attachment_unique {F : Rectangle} {s : ℕ} {u v c : Vertex}
    (hu : Leaf F s u) (hv : Leaf F s v)
    (huc : SunAdj F s u c) (hvc : SunAdj F s v c) : u = v := by
  have hnc_u := leaf_not_core hu
  have hnc_v := leaf_not_core hv
  have hc : Core F s c := huc.2.resolve_left hnc_u
  exact core_noncore_neighbor_unique hc hnc_u hnc_v (adj_symm huc.1) (adj_symm hvc.1)

theorem leaves_not_sun_adjacent {F : Rectangle} {s : ℕ} {u v : Vertex}
    (hu : Leaf F s u) (hv : Leaf F s v) : ¬ SunAdj F s u v := by
  intro h
  exact h.2.elim (leaf_not_core hu) (leaf_not_core hv)

/-- A walk whose edges all belong to the actual sun graph. -/
inductive SunWalk (F : Rectangle) (s : ℕ) : Vertex → Vertex → ℕ → Prop where
  | nil (v : Vertex) : SunWalk F s v v 0
  | cons {u v w : Vertex} {n : ℕ} :
      SunAdj F s u v → SunWalk F s v w n → SunWalk F s u w (n + 1)

theorem SunWalk.toWalk {F : Rectangle} {s n : ℕ} {u v : Vertex}
    (h : SunWalk F s u v n) : Walk u v n := by
  induction h with
  | nil v => exact Walk.nil v
  | cons h _ ih => exact Walk.cons h.1 ih

/-- Distinct leaves are separated by at least three sun edges. -/
theorem SunWalk.between_leaves_length {F : Rectangle} {s n : ℕ} {u v : Vertex}
    (h : SunWalk F s u v n) (hu : Leaf F s u) (hv : Leaf F s v)
    (hne : u ≠ v) : 3 ≤ n := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons huv hvw =>
      cases hvw with
      | nil => exact False.elim (leaves_not_sun_adjacent hu hv huv)
      | cons hvz hzw =>
          cases hzw with
          | nil =>
              exact False.elim (hne (leaf_attachment_unique hu hv huv (sunAdj_symm hvz)))
          | cons _ _ => omega

/-- Consecutive vertices follow edges of a specified graph. -/
def ListWalk (E : Vertex → Vertex → Prop) : List Vertex → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => E u v ∧ ListWalk E (v :: rest)

/-- An unoriented edge set is represented here by either oriented traversal.
The eventual finite enumerator must quotient or canonically orient these
representatives before counting them. -/
structure BoundaryPath (F : Rectangle) (s : ℕ) where
  vertices : List Vertex
  start : Vertex
  finish : Vertex
  head_eq : vertices.head? = some start
  last_eq : vertices.getLast? = some finish
  nodup : vertices.Nodup
  consecutive : ListWalk (SunAdj F s) vertices
  start_leaf : Leaf F s start
  finish_leaf : Leaf F s finish
  distinct : start ≠ finish

def BoundaryPath.length {F : Rectangle} {s : ℕ} (p : BoundaryPath F s) : ℕ :=
  p.vertices.length - 1

/-- A simple closed traversal, without repeating its initial vertex at the end. -/
structure SimpleLoop (F : Rectangle) (s : ℕ) where
  vertices : List Vertex
  start : Vertex
  finish : Vertex
  head_eq : vertices.head? = some start
  last_eq : vertices.getLast? = some finish
  nodup : vertices.Nodup
  consecutive : ListWalk (SunAdj F s) vertices
  closing : SunAdj F s finish start
  nondegenerate : 3 ≤ vertices.length

def SimpleLoop.length {F : Rectangle} {s : ℕ} (p : SimpleLoop F s) : ℕ :=
  p.vertices.length

end RootedKP.Honeycomb
