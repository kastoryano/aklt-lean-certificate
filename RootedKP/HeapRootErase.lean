import RootedKP.HeapDecomposition
import Mathlib.Logic.Equiv.Option
import Mathlib.Algebra.BigOperators.Option

/-! Erasing the unique least occurrence, respecting labelled heap isomorphism. -/

universe u

namespace RootedKP.Heaps
namespace FiniteHeap

open scoped BigOperators

variable {P : Type u} {R : P → P → Prop}

noncomputable def root (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) : H.Carrier :=
  Classical.choose hr

theorem root_label (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) :
    H.label (H.root hr) = p := (Classical.choose_spec hr).1

theorem root_le (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) (x : H.Carrier) :
    H.order.le (H.root hr) x := (Classical.choose_spec hr).2 x

theorem root_minimal (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) :
    @IsMin H.Carrier H.order.toLE (H.root hr) := by
  intro x _
  exact H.root_le hr x

noncomputable def eraseRoot (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) :
    FiniteHeap P R := by
  classical
  letI := H.order
  letI := H.finite
  exact {
    Carrier := {x : H.Carrier // x ≠ H.root hr}
    finite := inferInstance
    order := inferInstance
    label := fun x => H.label x
    isHeap := isHeap_subtype_of_convex H.isHeap (fun x => x ≠ H.root hr) (by
      intro x y z hx _ hxy _ hy
      apply hx
      subst y
      exact le_antisymm hxy (H.root_le hr x))
  }

theorem eraseRoot_size_succ (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) :
    (H.eraseRoot hr).size + 1 = H.size := by
  classical
  letI := H.finite
  letI := (H.eraseRoot hr).finite
  let e : Option (H.eraseRoot hr).Carrier ≃ H.Carrier := Equiv.optionSubtypeNe (H.root hr)
  simpa only [FiniteHeap.size, Fintype.card_option] using Fintype.card_congr e

theorem weight_eraseRoot {W : Type*} [CommMonoid W] (H : FiniteHeap P R)
    {p : P} (hr : H.IsRootedAt p) (w : P → W) :
    H.weight w = w p * (H.eraseRoot hr).weight w := by
  classical
  letI := H.finite
  letI := (H.eraseRoot hr).finite
  let e : Option (H.eraseRoot hr).Carrier ≃ H.Carrier := Equiv.optionSubtypeNe (H.root hr)
  have h := Fintype.prod_equiv e
    (fun o => w (H.label (e o)))
    (fun x => w (H.label x)) (fun _ => rfl)
  change (∏ x : H.Carrier, w (H.label x)) =
    w p * ∏ x : (H.eraseRoot hr).Carrier, w ((H.eraseRoot hr).label x)
  rw [← h, Fintype.prod_option]
  change w (H.label (H.root hr)) *
    (∏ x : (H.eraseRoot hr).Carrier, w (H.label x.val)) = _
  rw [H.root_label hr]
  rfl

theorem eraseRoot_minimum_incompatible (H : FiniteHeap P R) {p : P}
    (hr : H.IsRootedAt p) (x : (H.eraseRoot hr).Carrier)
    (hx : @IsMin (H.eraseRoot hr).Carrier (H.eraseRoot hr).order.toLE x) :
    R p ((H.eraseRoot hr).label x) := by
  letI := H.order
  have h := new_minimum_incompatible H.isHeap (H.root_le hr) x.property.symm
    (fun y hy hyx => hx (show (H.eraseRoot hr).order.le ⟨y, hy⟩ x from hyx))
  simpa only [eraseRoot, H.root_label hr] using h

theorem eraseRoot_group_size_zero [LinearOrder P] (H : FiniteHeap P R) {p q : P}
    (hr : H.IsRootedAt p) (hnot : ¬R p q) : ((H.eraseRoot hr).group q).size = 0 := by
  let K := H.eraseRoot hr
  letI := K.order
  letI := (K.group q).finite
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  obtain ⟨m, hm, _, hlabel⟩ := K.assignment.realized x.val
  have hdep := H.eraseRoot_minimum_incompatible hr m hm
  have hmq : K.label m = q := hlabel.trans x.property
  exact hnot (hmq ▸ hdep)

namespace Iso

theorem root_eq {H K : FiniteHeap P R} (e : Iso H K) {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p) : e.toEquiv (H.root hr) = K.root hs := by
  letI := K.order
  apply le_antisymm
  · simpa using (e.le_iff _ _).mp (H.root_le hr (e.toEquiv.symm (K.root hs)))
  · exact K.root_le hs _

noncomputable def eraseRootIso {H K : FiniteHeap P R} (e : Iso H K) {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p) : Iso (H.eraseRoot hr) (K.eraseRoot hs) where
  toEquiv := {
    toFun := fun x => ⟨e.toEquiv x.val, by
      intro h
      apply x.property
      exact e.toEquiv.injective (h.trans (e.root_eq hr hs).symm)⟩
    invFun := fun y => ⟨e.toEquiv.symm y.val, by
      intro h
      apply y.property
      have h' := congrArg e.toEquiv h
      simpa only [Equiv.apply_symm_apply, e.root_eq hr hs] using h'⟩
    left_inv := fun x => Subtype.ext (e.toEquiv.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (e.toEquiv.apply_symm_apply y.val)
  }
  label_eq x := e.label_eq x.val
  le_iff x y := e.le_iff x.val y.val

end Iso

/-- Extend an isomorphism of the remainders by mapping the erased root to the
erased root.  Both roots have the same prescribed label. -/
noncomputable def extendEraseEquiv {H K : FiniteHeap P R} {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p)
    (e : Iso (H.eraseRoot hr) (K.eraseRoot hs)) : H.Carrier ≃ K.Carrier := by
  classical
  exact (Equiv.optionSubtypeNe (H.root hr)).symm.trans
    ((Equiv.optionCongr e.toEquiv).trans (Equiv.optionSubtypeNe (K.root hs)))

theorem extendErase_root {H K : FiniteHeap P R} {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p)
    (e : Iso (H.eraseRoot hr) (K.eraseRoot hs)) :
    extendEraseEquiv hr hs e (H.root hr) = K.root hs := by
  classical
  change (Equiv.optionSubtypeNe (K.root hs))
    (Option.map e.toEquiv ((Equiv.optionSubtypeNe (H.root hr)).symm (H.root hr))) = _
  rw [Equiv.optionSubtypeNe_symm_self]
  rfl

theorem extendErase_nonroot {H K : FiniteHeap P R} {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p)
    (e : Iso (H.eraseRoot hr) (K.eraseRoot hs)) (x : (H.eraseRoot hr).Carrier) :
    extendEraseEquiv hr hs e x.val = (e.toEquiv x).val := by
  classical
  change (Equiv.optionSubtypeNe (K.root hs))
    (Option.map e.toEquiv ((Equiv.optionSubtypeNe (H.root hr)).symm x.val)) = _
  rw [Equiv.optionSubtypeNe_symm_of_ne x.property]
  rfl

noncomputable def Iso.ofEraseRoot {H K : FiniteHeap P R} {p : P}
    (hr : H.IsRootedAt p) (hs : K.IsRootedAt p)
    (e : Iso (H.eraseRoot hr) (K.eraseRoot hs)) : Iso H K where
  toEquiv := extendEraseEquiv hr hs e
  label_eq x := by
    classical
    by_cases hx : x = H.root hr
    · subst x
      rw [extendErase_root, H.root_label hr, K.root_label hs]
    · rw [extendErase_nonroot hr hs e ⟨x, hx⟩]
      exact e.label_eq ⟨x, hx⟩
  le_iff x y := by
    classical
    letI := H.order
    letI := K.order
    by_cases hx : x = H.root hr
    · subst x
      rw [extendErase_root]
      exact iff_of_true (H.root_le hr _) (K.root_le hs _)
    by_cases hy : y = H.root hr
    · subst y
      rw [extendErase_root, extendErase_nonroot hr hs e ⟨x, hx⟩]
      constructor
      · intro h
        exact (hx (le_antisymm h (H.root_le hr x))).elim
      · intro h
        exact ((e.toEquiv ⟨x, hx⟩).property
          (le_antisymm h (K.root_le hs _))).elim
    · rw [extendErase_nonroot hr hs e ⟨x, hx⟩,
        extendErase_nonroot hr hs e ⟨y, hy⟩]
      exact e.le_iff ⟨x, hx⟩ ⟨y, hy⟩

end FiniteHeap

namespace Heap

variable {P : Type u} {R : P → P → Prop}

/-- Delete the least occurrence when the heap has the specified root; return the
original heap otherwise.  Only the rooted branch is used in rooted sums. -/
noncomputable def deleteRoot (h : Heap P R) (p : P) : Heap P R := by
  classical
  refine Quotient.lift
    (fun H : FiniteHeap P R => if hr : H.IsRootedAt p then ofFinite (H.eraseRoot hr)
      else ofFinite H) ?_ h
  intro H K hiso
  obtain ⟨e⟩ := hiso
  by_cases hr : H.IsRootedAt p
  · have hs := (e.rooted_iff p).mp hr
    simp only [dif_pos hr, dif_pos hs]
    exact Quotient.sound ⟨e.eraseRootIso hr hs⟩
  · have hs : ¬K.IsRootedAt p := fun hk => hr ((e.rooted_iff p).mpr hk)
    simp only [dif_neg hr, dif_neg hs]
    exact Quotient.sound ⟨e⟩

theorem deleteRoot_ofFinite (H : FiniteHeap P R) {p : P} (hr : H.IsRootedAt p) :
    (ofFinite H).deleteRoot p = ofFinite (H.eraseRoot hr) := by
  classical
  change (if h : H.IsRootedAt p then ofFinite (H.eraseRoot h) else ofFinite H) = _
  rw [dif_pos hr]

theorem deleteRoot_injective_on_root {p : P} {h k : Heap P R}
    (hr : h.IsRootedAt p) (hs : k.IsRootedAt p)
    (heq : h.deleteRoot p = k.deleteRoot p) : h = k := by
  induction h using Quotient.inductionOn with
  | _ H =>
    induction k using Quotient.inductionOn with
    | _ K =>
      have hH : H.IsRootedAt p := hr
      have hK : K.IsRootedAt p := hs
      rw [deleteRoot_ofFinite H hH, deleteRoot_ofFinite K hK] at heq
      obtain ⟨e⟩ := Quotient.exact heq
      exact Quotient.sound ⟨FiniteHeap.Iso.ofEraseRoot hH hK e⟩

theorem deleteRoot_size_succ {h : Heap P R} {p : P} (hr : h.IsRootedAt p) :
    (h.deleteRoot p).size + 1 = h.size := by
  induction h using Quotient.inductionOn with
  | _ H =>
    rw [deleteRoot_ofFinite H hr]
    exact H.eraseRoot_size_succ hr

theorem weight_deleteRoot {W : Type*} [CommMonoid W] {h : Heap P R} {p : P}
    (hr : h.IsRootedAt p) (w : P → W) : weight w h = w p * weight w (h.deleteRoot p) := by
  induction h using Quotient.inductionOn with
  | _ H =>
    rw [deleteRoot_ofFinite H hr]
    exact H.weight_eraseRoot hr w

theorem deleteRoot_group_size_zero [LinearOrder P] {h : Heap P R} {p q : P}
    (hr : h.IsRootedAt p) (hnot : ¬R p q) : ((h.deleteRoot p).group q).size = 0 := by
  induction h using Quotient.inductionOn with
  | _ H =>
    rw [deleteRoot_ofFinite H hr]
    exact H.eraseRoot_group_size_zero hr hnot

end Heap
end RootedKP.Heaps
