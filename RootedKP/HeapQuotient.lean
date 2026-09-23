import RootedKP.Heaps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite heaps modulo labelled order isomorphism

Carriers are arbitrary finite types.  Taking the quotient identifies all choices
of occurrence names.  The resulting type lives one universe above the label
type; infinite sums in mathlib permit such index types.
-/

universe u

namespace RootedKP.Heaps

open scoped BigOperators

structure FiniteHeap (P : Type u) (R : P → P → Prop) where
  Carrier : Type u
  finite : Fintype Carrier
  order : PartialOrder Carrier
  label : Carrier → P
  isHeap : @IsHeap P Carrier order R label

namespace FiniteHeap

variable {P : Type u} {R : P → P → Prop}

/-- An occurrence-renaming preserving labels and the complete partial order. -/
structure Iso (H K : FiniteHeap P R) where
  toEquiv : H.Carrier ≃ K.Carrier
  label_eq : ∀ x, K.label (toEquiv x) = H.label x
  le_iff : ∀ x y, H.order.le x y ↔ K.order.le (toEquiv x) (toEquiv y)

namespace Iso

def refl (H : FiniteHeap P R) : Iso H H where
  toEquiv := Equiv.refl _
  label_eq _ := rfl
  le_iff _ _ := Iff.rfl

def symm {H K : FiniteHeap P R} (e : Iso H K) : Iso K H where
  toEquiv := e.toEquiv.symm
  label_eq y := by
    simpa using (e.label_eq (e.toEquiv.symm y)).symm
  le_iff x y := by
    simpa using (e.le_iff (e.toEquiv.symm x) (e.toEquiv.symm y)).symm

def trans {H K L : FiniteHeap P R} (e : Iso H K) (f : Iso K L) : Iso H L where
  toEquiv := e.toEquiv.trans f.toEquiv
  label_eq x := (f.label_eq (e.toEquiv x)).trans (e.label_eq x)
  le_iff x y := (e.le_iff x y).trans (f.le_iff (e.toEquiv x) (e.toEquiv y))

end Iso

def isoSetoid (P : Type u) (R : P → P → Prop) : Setoid (FiniteHeap P R) where
  r H K := Nonempty (Iso H K)
  iseqv := ⟨fun H => ⟨Iso.refl H⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

def size (H : FiniteHeap P R) : ℕ := @Fintype.card H.Carrier H.finite

def IsRootedAt (H : FiniteHeap P R) (p : P) : Prop :=
  ∃ r : H.Carrier, H.label r = p ∧ ∀ x, H.order.le r x

theorem root_label_unique (H : FiniteHeap P R) {p q : P}
    (hp : H.IsRootedAt p) (hq : H.IsRootedAt q) : p = q := by
  letI := H.order
  obtain ⟨r, hr, hleast⟩ := hp
  obtain ⟨s, hs, hleast'⟩ := hq
  have hrs : r = s := le_antisymm (hleast s) (hleast' r)
  exact hr.symm.trans ((congrArg H.label hrs).trans hs)

noncomputable def weight {W : Type*} [CommMonoid W]
    (H : FiniteHeap P R) (w : P → W) : W :=
  letI := H.finite
  ∏ x, w (H.label x)

namespace Iso

theorem size_eq {H K : FiniteHeap P R} (e : Iso H K) : H.size = K.size := by
  letI := H.finite
  letI := K.finite
  exact Fintype.card_congr e.toEquiv

theorem rooted_iff {H K : FiniteHeap P R} (e : Iso H K) (p : P) :
    H.IsRootedAt p ↔ K.IsRootedAt p := by
  have forward : ∀ {H K : FiniteHeap P R}, Iso H K → H.IsRootedAt p → K.IsRootedAt p := by
    intro H K f ⟨r, hr, hleast⟩
    refine ⟨f.toEquiv r, (f.label_eq r).trans hr, ?_⟩
    intro y
    simpa using (f.le_iff r (f.toEquiv.symm y)).mp (hleast (f.toEquiv.symm y))
  exact ⟨forward e, forward e.symm⟩

theorem weight_eq {W : Type*} [CommMonoid W] {H K : FiniteHeap P R}
    (e : Iso H K) (w : P → W) : H.weight w = K.weight w := by
  letI := H.finite
  letI := K.finite
  exact Fintype.prod_equiv e.toEquiv _ _ (fun x => congrArg w (e.label_eq x).symm)

noncomputable def ofEmpty {H K : FiniteHeap P R} (hH : H.size = 0) (hK : K.size = 0) :
    Iso H K := by
  letI := H.finite
  letI := K.finite
  letI : IsEmpty H.Carrier := Fintype.card_eq_zero_iff.mp hH
  letI : IsEmpty K.Carrier := Fintype.card_eq_zero_iff.mp hK
  exact {
    toEquiv := Equiv.equivOfIsEmpty H.Carrier K.Carrier
    label_eq := fun x => isEmptyElim x
    le_iff := fun x _ => isEmptyElim x
  }

end Iso

end FiniteHeap

/-- The actual heap type, with occurrence names removed. -/
abbrev Heap (P : Type u) (R : P → P → Prop) := Quotient (FiniteHeap.isoSetoid P R)

namespace Heap

variable {P : Type u} {R : P → P → Prop}

abbrev ofFinite (H : FiniteHeap P R) : Heap P R := Quotient.mk _ H

theorem ofFinite_eq_iff (H K : FiniteHeap P R) :
    ofFinite H = ofFinite K ↔ Nonempty (FiniteHeap.Iso H K) :=
  Quotient.eq

def size : Heap P R → ℕ := Quotient.lift FiniteHeap.size (fun _ _ ⟨e⟩ => e.size_eq)

def IsRootedAt (p : P) : Heap P R → Prop :=
  Quotient.lift (fun H => H.IsRootedAt p) (fun _ _ ⟨e⟩ => propext (e.rooted_iff p))

theorem root_label_unique (h : Heap P R) {p q : P}
    (hp : h.IsRootedAt p) (hq : h.IsRootedAt q) : p = q := by
  induction h using Quotient.inductionOn with
  | _ H => exact H.root_label_unique hp hq

noncomputable def weight {W : Type*} [CommMonoid W] (w : P → W) : Heap P R → W :=
  Quotient.lift (fun H => H.weight w) (fun _ _ ⟨e⟩ => e.weight_eq w)

theorem eq_of_size_zero {h k : Heap P R} (hh : h.size = 0) (hk : k.size = 0) : h = k := by
  induction h using Quotient.inductionOn with
  | _ H =>
    induction k using Quotient.inductionOn with
    | _ K => exact Quotient.sound ⟨FiniteHeap.Iso.ofEmpty hh hk⟩

theorem weight_of_size_zero {W : Type*} [CommMonoid W] (w : P → W)
    {h : Heap P R} (hh : h.size = 0) : weight w h = 1 := by
  induction h using Quotient.inductionOn with
  | _ H =>
    letI := H.finite
    letI : IsEmpty H.Carrier := Fintype.card_eq_zero_iff.mp hh
    exact Finset.prod_eq_one (fun x _ => isEmptyElim x)

end Heap

/-- Heaps with one least occurrence, of the specified polymer label. -/
abbrev RootedHeap {P : Type u} (R : P → P → Prop) (p : P) :=
  {h : Heap P R // h.IsRootedAt p}

/-- A convenient disjoint union when a theorem needs an explicit root function. -/
abbrev AllRootedHeaps (P : Type u) (R : P → P → Prop) := Σ p : P, RootedHeap R p

end RootedKP.Heaps
