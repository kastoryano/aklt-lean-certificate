import RootedKP.Polymers
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Interval

/-!
# The regional polymer alphabet is genuinely finite

The finite universe below is constructed from the actual rectangle, halo and
sun edges. It supplies finiteness without imposing a length cutoff on polymers.
-/

namespace RootedKP.AKLT

open Honeycomb

def faceSet (F : Rectangle) (s : ℕ) : Finset Face :=
  ((Finset.Icc (F.qmin - s) (F.qmax + s)).product
    (Finset.Icc (F.rmin - s) (F.rmax + s))).filter
      (fun f => F.qmin + F.rmin - s ≤ f.1 + f.2 ∧
        f.1 + f.2 ≤ F.qmax + F.rmax + s)

@[simp] theorem mem_faceSet (F : Rectangle) (s : ℕ) (f : Face) :
    f ∈ faceSet F s ↔ FaceHalo F s f := by
  rcases f with ⟨q, r⟩
  simp [faceSet, FaceHalo, and_assoc]

def faceVertices (f : Face) : Finset Vertex :=
  {.a f.1 f.2, .b (f.1 - 1) f.2, .a (f.1 - 1) f.2,
   .b (f.1 - 1) (f.2 - 1), .a f.1 (f.2 - 1), .b f.1 (f.2 - 1)}

@[simp] theorem mem_faceVertices (f : Face) (v : Vertex) :
    v ∈ faceVertices f ↔ Incident v f := by
  cases f with
  | mk q r =>
      cases v <;> simp [faceVertices, Incident] <;> omega

def coreSet (F : Rectangle) (s : ℕ) : Finset Vertex :=
  (faceSet F s).biUnion faceVertices

@[simp] theorem mem_coreSet (F : Rectangle) (s : ℕ) (v : Vertex) :
    v ∈ coreSet F s ↔ Core F s v := by
  simp [coreSet, Core]

def sunEdges (F : Rectangle) (s : ℕ) : Finset Edge :=
  (coreSet F s).biUnion (fun u => (neighbors u).image (fun v => s(u, v)))

theorem sun_edge_mem {F : Rectangle} {s : ℕ} {u v : Vertex}
    (h : SunAdj F s u v) : s(u, v) ∈ sunEdges F s := by
  rcases h.2 with hu | hv
  · exact Finset.mem_biUnion.mpr ⟨u, (mem_coreSet F s u).mpr hu,
      Finset.mem_image.mpr ⟨v, (mem_neighbors u v).mpr h.1, rfl⟩⟩
  · have hs : s(v, u) = s(u, v) := Sym2.eq_swap
    exact Finset.mem_biUnion.mpr ⟨v, (mem_coreSet F s v).mpr hv,
      Finset.mem_image.mpr ⟨u, (mem_neighbors v u).mpr (adj_symm h.1), hs⟩⟩

theorem traversalEdges_subset {F : Rectangle} {s : ℕ} {vs : List Vertex}
    (h : ListWalk (SunAdj F s) vs) : traversalEdges vs ⊆ sunEdges F s := by
  induction vs with
  | nil => simp [traversalEdges]
  | cons u rest ih =>
      cases rest with
      | nil => simp [traversalEdges]
      | cons v rest =>
          obtain ⟨huv, hr⟩ := h
          exact Finset.insert_subset_iff.mpr ⟨sun_edge_mem huv, ih hr⟩

theorem Polymer.edges_subset (F : Rectangle) (p : Polymer F) :
    p.edges ⊆ sunEdges F haloRadius := by
  rcases p with ⟨kind, edges, h⟩
  cases kind with
  | path =>
      obtain ⟨walk, rfl⟩ := h
      exact traversalEdges_subset walk.consecutive
  | loop =>
      obtain ⟨walk, rfl⟩ := h
      exact Finset.insert_subset_iff.mpr
        ⟨sun_edge_mem walk.closing, traversalEdges_subset walk.consecutive⟩

def polymerCodes (F : Rectangle) : Finset (Kind × Finset Edge) :=
  ({Kind.path, Kind.loop} : Finset Kind).product (sunEdges F haloRadius).powerset

def Polymer.code (F : Rectangle) (p : Polymer F) :
    {code : Kind × Finset Edge // code ∈ polymerCodes F} :=
  ⟨(p.kind, p.edges), by
    apply Finset.mem_product.mpr
    constructor
    · cases p.kind <;> simp
    · exact Finset.mem_powerset.mpr (p.edges_subset F)⟩

theorem Polymer.code_injective (F : Rectangle) : Function.Injective (Polymer.code F) := by
  intro p q h
  have heq := congrArg Subtype.val h
  have hk := congrArg Prod.fst heq
  have he := congrArg Prod.snd heq
  cases p
  cases q
  simp only [Polymer.code] at hk he
  cases hk
  cases he
  rfl

instance (F : Rectangle) : Finite (Polymer F) :=
  Finite.of_injective (Polymer.code F) (Polymer.code_injective F)

noncomputable instance (F : Rectangle) : Fintype (Polymer F) := Fintype.ofFinite _

end RootedKP.AKLT
