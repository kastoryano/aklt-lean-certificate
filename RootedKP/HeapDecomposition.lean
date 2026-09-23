import RootedKP.HeapQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! Canonical owner groups and their behaviour under labelled heap isomorphism. -/

universe u

namespace RootedKP.Heaps

namespace FiniteHeap

open scoped BigOperators

variable {P : Type u} {R : P → P → Prop} [LinearOrder P]

noncomputable def assignment (H : FiniteHeap P R) :
    @MinimalAncestorLabelling P H.Carrier H.order inferInstance H.label := by
  letI := H.order
  letI := H.finite
  exact largestMinimalAncestorLabelling H.label

noncomputable def owner (H : FiniteHeap P R) : H.Carrier → P := by
  letI := H.order
  exact H.assignment.owner

noncomputable def group (H : FiniteHeap P R) (p : P) : FiniteHeap P R := by
  classical
  letI := H.order
  letI := H.finite
  exact {
    Carrier := {x : H.Carrier // H.owner x = p}
    finite := inferInstance
    order := inferInstance
    label := fun x => H.label x
    isHeap := H.assignment.group_isHeap H.isHeap p
  }

theorem group_rooted (H : FiniteHeap P R) (hself : ∀ p, R p p)
    {p : P} (hne : ∃ x, H.owner x = p) : (H.group p).IsRootedAt p := by
  letI := H.order
  exact H.assignment.group_has_least H.isHeap hself hne

namespace Iso

theorem map_isMin {H K : FiniteHeap P R} (e : Iso H K) {x : H.Carrier}
    (hx : @IsMin H.Carrier H.order.toLE x) :
    @IsMin K.Carrier K.order.toLE (e.toEquiv x) := by
  intro y hy
  have hyx : H.order.le (e.toEquiv.symm y) x := by
    apply (e.le_iff _ _).mpr
    simpa using hy
  have hxy := hx hyx
  simpa using (e.le_iff _ _).mp hxy

/-- Largest-minimal-ancestor labels are independent of occurrence names. -/
theorem owner_eq {H K : FiniteHeap P R} (e : Iso H K) (x : H.Carrier) :
    K.owner (e.toEquiv x) = H.owner x := by
  have forward : ∀ {H K : FiniteHeap P R} (f : Iso H K) (y : H.Carrier),
      H.owner y ≤ K.owner (f.toEquiv y) := by
    intro H K f y
    letI := H.order
    letI := K.order
    obtain ⟨m, hm, hmy, hlabel⟩ := H.assignment.realized y
    have h := K.assignment.greatest (f.toEquiv y) (f.toEquiv m)
      (f.map_isMin hm) ((f.le_iff _ _).mp hmy)
    simpa only [owner, f.label_eq, hlabel] using h
  exact le_antisymm (by simpa [Iso.symm] using forward e.symm (e.toEquiv x)) (forward e x)

/-- An isomorphism of heaps restricts to each canonical owner group. -/
noncomputable def groupIso {H K : FiniteHeap P R} (e : Iso H K) (p : P) :
    Iso (H.group p) (K.group p) where
  toEquiv := {
    toFun := fun x => ⟨e.toEquiv x.val, (e.owner_eq x.val).trans x.property⟩
    invFun := fun y => ⟨e.toEquiv.symm y.val, (e.symm.owner_eq y.val).trans y.property⟩
    left_inv := fun x => Subtype.ext (e.toEquiv.symm_apply_apply x.val)
    right_inv := fun y => Subtype.ext (e.toEquiv.apply_symm_apply y.val)
  }
  label_eq x := e.label_eq x.val
  le_iff x y := e.le_iff x.val y.val

end Iso

/-- Occurrences are the disjoint union of their owner groups. -/
noncomputable def groupEquiv (H : FiniteHeap P R) :
    H.Carrier ≃ Σ p : P, (H.group p).Carrier where
  toFun x := ⟨H.owner x, ⟨x, rfl⟩⟩
  invFun x := x.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨p, x, hx⟩
    cases hx
    rfl

theorem group_size_le (H : FiniteHeap P R) (p : P) : (H.group p).size ≤ H.size := by
  letI := H.finite
  letI := (H.group p).finite
  exact Fintype.card_le_of_injective (fun x : (H.group p).Carrier => x.val)
    Subtype.val_injective

/-- The weight factors exactly over the owner groups. -/
theorem weight_groups [Fintype P] {W : Type*} [CommMonoid W]
    (H : FiniteHeap P R) (w : P → W) : H.weight w = ∏ p, (H.group p).weight w := by
  letI := H.finite
  letI (p : P) := (H.group p).finite
  calc
    H.weight w = ∏ x : Σ p : P, (H.group p).Carrier, w ((H.group x.1).label x.2) :=
      Fintype.prod_equiv H.groupEquiv _ _ (fun _ => rfl)
    _ = ∏ p, (H.group p).weight w := by
      simp only [Fintype.prod_sigma, FiniteHeap.weight]

noncomputable def reassembleEquiv {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) : H.Carrier ≃ K.Carrier :=
  H.groupEquiv.trans ((Equiv.sigmaCongrRight (fun p => (e p).toEquiv)).trans
    K.groupEquiv.symm)

theorem reassemble_apply_at {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) (p : P) (x : (H.group p).Carrier) :
    reassembleEquiv e x.val = ((e p).toEquiv x).val := by
  rcases x with ⟨x, hx⟩
  cases hx
  rfl

theorem reassemble_owner {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) (x : H.Carrier) :
    K.owner (reassembleEquiv e x) = H.owner x :=
  ((e (H.owner x)).toEquiv ⟨x, rfl⟩).property

theorem reassemble_label {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) (x : H.Carrier) :
    K.label (reassembleEquiv e x) = H.label x :=
  (e (H.owner x)).label_eq ⟨x, rfl⟩

theorem reassemble_le {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) {x y : H.Carrier}
    (hxy : H.order.le x y) : K.order.le (reassembleEquiv e x) (reassembleEquiv e y) := by
  letI := H.order
  letI := K.order
  apply order_generated_by_dependencies H.isHeap
    (fun u v => K.order.le (reassembleEquiv e u) (reassembleEquiv e v))
    (fun _ => le_rfl) (fun _ _ _ h₁ h₂ => h₁.trans h₂) ?_ hxy
  intro u v hstep
  rcases (H.assignment.monotone hstep.1.le).eq_or_lt with heq | hlt
  · let u' : (H.group (H.owner u)).Carrier := ⟨u, rfl⟩
    let v' : (H.group (H.owner u)).Carrier := ⟨v, heq.symm⟩
    have hgroup : (H.group (H.owner u)).order.le u' v' := hstep.1.le
    rw [reassemble_apply_at e _ u', reassemble_apply_at e _ v']
    exact ((e (H.owner u)).le_iff u' v').mp hgroup
  · apply K.assignment.no_backward_dependency K.isHeap
    · change K.owner (reassembleEquiv e u) < K.owner (reassembleEquiv e v)
      change H.owner u < H.owner v at hlt
      simpa only [reassemble_owner] using hlt
    · simpa only [reassemble_label] using hstep.2

/-- The isomorphism classes of all owner groups determine the heap itself. -/
noncomputable def Iso.ofGroups {H K : FiniteHeap P R}
    (e : ∀ p, Iso (H.group p) (K.group p)) : Iso H K where
  toEquiv := reassembleEquiv e
  label_eq := reassemble_label e
  le_iff x y := by
    constructor
    · exact reassemble_le e
    · intro h
      have hback := reassemble_le (fun p => (e p).symm) h
      change H.order.le ((reassembleEquiv e).symm (reassembleEquiv e x))
        ((reassembleEquiv e).symm (reassembleEquiv e y)) at hback
      simpa using hback

end FiniteHeap

namespace Heap

open scoped BigOperators

variable {P : Type u} {R : P → P → Prop} [LinearOrder P]

/-- Canonical groups are well-defined on actual heaps, not just representatives. -/
noncomputable def group (h : Heap P R) (p : P) : Heap P R :=
  Quotient.lift (fun H : FiniteHeap P R => ofFinite (H.group p))
    (fun (H K : FiniteHeap P R) (hiso : Nonempty (FiniteHeap.Iso H K)) =>
      Quotient.sound ⟨(Classical.choice hiso).groupIso p⟩) h

/-- The canonical group encoding is injective on heaps modulo occurrence names. -/
theorem group_injective : Function.Injective (fun h : Heap P R => fun p => h.group p) := by
  intro h k heq
  induction h using Quotient.inductionOn with
  | _ H =>
    induction k using Quotient.inductionOn with
    | _ K =>
      have hgroups : ∀ p, Nonempty (FiniteHeap.Iso (H.group p) (K.group p)) := by
        intro p
        exact Quotient.exact (congrFun heq p)
      exact Quotient.sound ⟨FiniteHeap.Iso.ofGroups (fun p => Classical.choice (hgroups p))⟩

theorem group_size_le (h : Heap P R) (p : P) : (h.group p).size ≤ h.size := by
  induction h using Quotient.inductionOn with
  | _ H => exact H.group_size_le p

theorem group_rooted_of_size_pos (h : Heap P R) (p : P) (hself : ∀ p, R p p)
    (hn : 0 < (h.group p).size) : (h.group p).IsRootedAt p := by
  induction h using Quotient.inductionOn with
  | _ H =>
    letI := (H.group p).finite
    obtain ⟨x⟩ : Nonempty (H.group p).Carrier := Fintype.card_pos_iff.mp hn
    exact H.group_rooted hself ⟨x.val, x.property⟩

theorem weight_groups [Fintype P] {W : Type*} [CommMonoid W] (h : Heap P R) (w : P → W) :
    weight w h = ∏ p, weight w (h.group p) := by
  induction h using Quotient.inductionOn with
  | _ H => exact H.weight_groups w

end Heap

end RootedKP.Heaps
