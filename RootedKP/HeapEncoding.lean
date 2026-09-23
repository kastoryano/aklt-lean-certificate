import RootedKP.HeapRootErase
import Lean.Elab.Tactic.Omega

/-! The size-decreasing, weight-preserving encoding behind the rooted KP bound. -/

universe u

namespace RootedKP.Heaps

open scoped BigOperators
open scoped Classical

abbrev BoundedRootedHeap {P : Type u} (R : P → P → Prop) (n : ℕ) (p : P) :=
  {h : Heap P R // h.IsRootedAt p ∧ h.size ≤ n}

variable {P : Type u} {R : P → P → Prop} [LinearOrder P]

noncomputable def packGroup (hself : ∀ p, R p p) (n : ℕ) (h : Heap P R)
    (hsize : h.size ≤ n) (q : P) : Option (BoundedRootedHeap R n q) := by
  classical
  exact if hn : 0 < (h.group q).size then
    some ⟨h.group q, h.group_rooted_of_size_pos q hself hn,
      (h.group_size_le q).trans hsize⟩ else none

theorem group_eq_of_packGroup_eq (hself : ∀ p, R p p) (n : ℕ)
    {h k : Heap P R} (hh : h.size ≤ n) (hk : k.size ≤ n) (q : P)
    (heq : packGroup hself n h hh q = packGroup hself n k hk q) : h.group q = k.group q := by
  classical
  by_cases hpos : 0 < (h.group q).size
  · by_cases kpos : 0 < (k.group q).size
    · simp only [packGroup, dif_pos hpos, dif_pos kpos, Option.some.injEq] at heq
      exact congrArg Subtype.val heq
    · simp [packGroup, hpos, kpos] at heq
  · by_cases kpos : 0 < (k.group q).size
    · simp [packGroup, hpos, kpos] at heq
    · exact Heap.eq_of_size_zero (Nat.eq_zero_of_not_pos hpos) (Nat.eq_zero_of_not_pos kpos)

noncomputable def optionWeight {W : Type*} [CommMonoid W] (w : P → W)
    {n : ℕ} {q : P} (o : Option (BoundedRootedHeap R n q)) : W :=
  o.elim 1 (fun h => Heap.weight w h.val)

theorem optionWeight_packGroup {W : Type*} [CommMonoid W] (w : P → W)
    (hself : ∀ p, R p p) (n : ℕ) (h : Heap P R) (hh : h.size ≤ n) (q : P) :
    optionWeight w (packGroup hself n h hh q) = Heap.weight w (h.group q) := by
  classical
  by_cases hpos : 0 < (h.group q).size
  · simp [packGroup, hpos, optionWeight]
  · simp only [packGroup, dif_neg hpos, optionWeight, Option.elim_none]
    exact (Heap.weight_of_size_zero w (Nat.eq_zero_of_not_pos hpos)).symm

theorem deleted_size_le {n : ℕ} {p : P} (h : BoundedRootedHeap R (n + 1) p) :
    (h.val.deleteRoot p).size ≤ n := by
  have heq := Heap.deleteRoot_size_succ h.property.1
  have hle := h.property.2
  omega

/-- Every root-erased group has a different possible root label.  Empty groups
are encoded by `none`; nonempty groups are smaller rooted heaps. -/
noncomputable def encodeRooted (hself : ∀ p, R p p) {n : ℕ} {p : P}
    (h : BoundedRootedHeap R (n + 1) p) :
    ∀ q : {q : P // R p q}, Option (BoundedRootedHeap R n q.val) :=
  fun q => packGroup hself n (h.val.deleteRoot p) (deleted_size_le h) q.val

theorem encodeRooted_injective (hself : ∀ p, R p p) (n : ℕ) (p : P) :
    Function.Injective (encodeRooted hself (n := n) (p := p)) := by
  intro h k heq
  apply Subtype.ext
  apply Heap.deleteRoot_injective_on_root h.property.1 k.property.1
  apply Heap.group_injective
  funext q
  by_cases hR : R p q
  · exact group_eq_of_packGroup_eq hself n (deleted_size_le h) (deleted_size_le k) q
      (congrFun heq ⟨q, hR⟩)
  · exact Heap.eq_of_size_zero
      (Heap.deleteRoot_group_size_zero h.property.1 hR)
      (Heap.deleteRoot_group_size_zero k.property.1 hR)

/-- Encoding preserves the full occurrence weight, including the erased root. -/
theorem weight_encodeRooted [Fintype P] {W : Type*} [CommMonoid W]
    (w : P → W) (hself : ∀ p, R p p) {n : ℕ} {p : P}
    (h : BoundedRootedHeap R (n + 1) p) :
    Heap.weight w h.val = w p * ∏ q : {q : P // R p q},
      optionWeight w (encodeRooted hself h q) := by
  classical
  rw [Heap.weight_deleteRoot h.property.1 w, Heap.weight_groups]
  congr 1
  have outside : (∏ q : {q : P // ¬R p q},
      Heap.weight w ((h.val.deleteRoot p).group q.val)) = 1 := by
    apply Finset.prod_eq_one
    intro q _
    exact Heap.weight_of_size_zero w
      (Heap.deleteRoot_group_size_zero h.property.1 q.property)
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun q : P => R p q)
    (fun q => Heap.weight w ((h.val.deleteRoot p).group q))
  rw [outside, mul_one] at hp
  rw [← hp]
  apply Finset.prod_congr rfl
  intro q _
  exact (optionWeight_packGroup w hself n (h.val.deleteRoot p) (deleted_size_le h) q.val).symm

end RootedKP.Heaps
