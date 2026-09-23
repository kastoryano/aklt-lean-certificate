import RootedKP.HeapEncoding
import RootedKP.AbstractKPENNReal
import RootedKP.ENNRealProducts

/-!
# Rooted KP for actual finite heaps

The combinatorial encoding is proved in `HeapEncoding`; no product recursion or
cluster expansion is assumed here.  All sums initially take values in ENNReal.
-/

universe u

namespace RootedKP.Heaps

open scoped BigOperators ENNReal Classical

variable {P : Type u} {R : P → P → Prop} [LinearOrder P]

noncomputable def boundedHeapMass (v : P → ℝ≥0∞) (n : ℕ) (p : P) : ℝ≥0∞ :=
  ∑' h : BoundedRootedHeap R n p, Heap.weight v h.val

noncomputable def rootedHeapMass (v : P → ℝ≥0∞) (p : P) : ℝ≥0∞ :=
  ∑' h : RootedHeap R p, Heap.weight v h.val

theorem boundedHeapMass_zero (v : P → ℝ≥0∞) (p : P) :
    boundedHeapMass (R := R) v 0 p = 0 := by
  haveI : IsEmpty (BoundedRootedHeap R 0 p) := ⟨fun h => by
    have heq := Heap.deleteRoot_size_succ h.property.1
    have hle := h.property.2
    omega⟩
  simp [boundedHeapMass]

/-- The rooted heap product recursion is a consequence of the proved injective
encoding, with exact occurrence weights. -/
theorem boundedHeapMass_step [Fintype P] (v : P → ℝ≥0∞) (hself : ∀ p, R p p)
    (n : ℕ) (p : P) :
    boundedHeapMass (R := R) v (n + 1) p ≤
      v p * ∏ q : {q : P // R p q}, (1 + boundedHeapMass (R := R) v n q.val) := by
  let weightChoices := fun f : ∀ q : {q : P // R p q}, Option (BoundedRootedHeap R n q.val) =>
    ∏ q, optionWeight v (f q)
  calc
    boundedHeapMass (R := R) v (n + 1) p =
        ∑' h : BoundedRootedHeap R (n + 1) p,
          v p * weightChoices (encodeRooted hself h) := by
      apply tsum_congr
      intro h
      exact weight_encodeRooted v hself h
    _ = v p * ∑' h : BoundedRootedHeap R (n + 1) p,
        weightChoices (encodeRooted hself h) := ENNReal.tsum_mul_left
    _ ≤ v p * ∑' f, weightChoices f :=
      mul_le_mul le_rfl
        (ENNReal.tsum_comp_le_tsum_of_injective (encodeRooted_injective hself n p) weightChoices)
        zero_le zero_le
    _ ≤ v p * ∏ q : {q : P // R p q},
        ∑' o : Option (BoundedRootedHeap R n q.val), optionWeight v o :=
      mul_le_mul le_rfl (ennreal_tsum_pi_le (fun _ o => optionWeight v o)) zero_le zero_le
    _ = v p * ∏ q : {q : P // R p q},
        (1 + boundedHeapMass (R := R) v n q.val) := by
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      exact ennreal_tsum_option (fun h : BoundedRootedHeap R n q.val => Heap.weight v h.val)

def boundedRootedEquiv (n : ℕ) (p : P) :
    {h : RootedHeap R p // h.val.size ≤ n} ≃ BoundedRootedHeap R n p where
  toFun h := ⟨h.val.val, h.val.property, h.property⟩
  invFun h := ⟨⟨h.val, h.property.1⟩, h.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rootedHeapMass_le_of_bounded (v : P → ℝ≥0∞) (p : P) {B : ℝ≥0∞}
    (hbound : ∀ n, boundedHeapMass (R := R) v n p ≤ B) :
    rootedHeapMass (R := R) v p ≤ B := by
  apply tsum_le_of_bounded_size (fun h : RootedHeap R p => h.val.size)
    (fun h => Heap.weight v h.val)
  intro n
  calc
    (∑' h : {h : RootedHeap R p // h.val.size ≤ n}, Heap.weight v h.val.val) =
        boundedHeapMass (R := R) v n p :=
      (boundedRootedEquiv (R := R) n p).tsum_eq
        (fun h : BoundedRootedHeap R n p => Heap.weight v h.val)
    _ ≤ B := hbound n

/-- Full rooted KP bound for heaps over a finite polymer set.  Self-incompatibility
is explicit.  The numerical KP assumption is exactly the `kp` field of `K`.
There is no assumed heap recursion, rooted bound, convergence, or cluster formula. -/
theorem rooted_heap_KP [Fintype P] (K : RootedKP.KPData P)
    (hself : ∀ p, p ∈ K.neighbours p) (p : P) :
    rootedHeapMass (R := fun p q => q ∈ K.neighbours p)
      (fun q => ENNReal.ofReal (K.activity q)) p ≤ ENNReal.ofReal (K.budget p) := by
  let dep : P → P → Prop := fun p q => q ∈ K.neighbours p
  let v : P → ℝ≥0∞ := fun q => ENNReal.ofReal (K.activity q)
  have hbounded : ∀ n p, boundedHeapMass (R := dep) v n p ≤ ENNReal.ofReal (K.budget p) := by
    apply K.ennreal_mass_le_budget_of_product_recursion (boundedHeapMass (R := dep) v)
    · exact boundedHeapMass_zero v
    · intro n q
      rw [Finset.prod_subtype (K.neighbours q) (fun _ => Iff.rfl)]
      exact boundedHeapMass_step v hself n q
  exact rootedHeapMass_le_of_bounded v p (fun n => hbounded n p)

/-- Application-facing form with the incompatibility relation and real weights
given explicitly.  The arbitrary linear order is used only to choose the
canonical decomposition; it does not occur in the resulting heap mass. -/
theorem rooted_heap_KP_of_criterion [Fintype P] (R : P → P → Prop)
    (v a : P → ℝ) (hv : ∀ p, 0 ≤ v p) (ha : ∀ p, 0 ≤ a p)
    (hself : ∀ p, R p p)
    (hKP : ∀ p, ∑ q ∈ Finset.univ.filter (R p), v q * Real.exp (a q) ≤ a p)
    (p : P) :
    rootedHeapMass (R := R) (fun q => ENNReal.ofReal (v q)) p ≤
      ENNReal.ofReal (v p * Real.exp (a p)) := by
  let K : RootedKP.KPData P := {
    neighbours := fun p => Finset.univ.filter (R p)
    activity := v
    cost := a
    activity_nonneg := hv
    cost_nonneg := ha
    kp := hKP
  }
  have hselfK : ∀ p, p ∈ K.neighbours p := by
    intro q
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hself q
  have hR : (fun p q => q ∈ K.neighbours p) = R := by
    funext q r
    exact propext (by simp only [K, Finset.mem_filter, Finset.mem_univ, true_and])
  have h := rooted_heap_KP K hselfK p
  rw [hR] at h
  exact h

end RootedKP.Heaps
