import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Int

/-!
# Counting two-spaced endpoint candidates on an unwrapped boundary arc

The cyclic geometry has to supply the unwrapping and its length bound. The
cardinality estimate below is proved directly, with no assumed counting lemma.
-/

namespace RootedKP.EndpointCounting

open scoped BigOperators

/-- An integer interval of length `m` contains at most `m/2+1` selected points
when distinct selected points have separation at least two. -/
theorem two_spaced_card (s : Finset ℤ) (lo hi : ℤ) (horder : lo ≤ hi)
    (hrange : ∀ x ∈ s, lo ≤ x ∧ x ≤ hi)
    (hspace : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 ≤ |x - y|) :
    2 * s.card ≤ (hi - lo).toNat + 2 := by
  let f : ℤ → ℕ := fun x => (x - lo).toNat / 2
  have hinj : Set.InjOn f (s : Set ℤ) := by
    intro x hx y hy heq
    by_contra hne
    have hs := hspace x hx y hy hne
    have hxrange := hrange x hx
    have hyrange := hrange y hy
    dsimp [f] at heq
    by_cases hxy : 0 ≤ x - y
    · rw [abs_of_nonneg hxy] at hs
      omega
    · rw [abs_of_neg (lt_of_not_ge hxy)] at hs
      omega
  have hsub : s.image f ⊆ Finset.range ((hi - lo).toNat / 2 + 1) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hxrange := hrange x hx
    simp only [Finset.mem_range]
    dsimp [f]
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  omega

/-- The collar padding and the `12d` collapsed edges produce the coefficient
`c_n = n - 1 + 6d` after counting two-spaced candidates. -/
theorem padded_arc_count (s : Finset ℤ) (lo hi : ℤ) (L n d : ℕ)
    (hn : 2 ≤ n) (horder : lo ≤ hi)
    (hrange : ∀ x ∈ s, lo ≤ x ∧ x ≤ hi)
    (hspace : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 ≤ |x - y|)
    (hlength : (hi - lo).toNat ≤ L + 2 * (n - 2) + 12 * d) :
    2 * s.card ≤ L + 2 * (n - 1 + 6 * d) := by
  have hc := two_spaced_card s lo hi horder hrange hspace
  omega

/-- Splitting a root into collar components costs only one endpoint allowance
if every deleted interior excursion pays the two new endpoint allowances. -/
theorem charge_interior_excursions {ι : Type*} (parts : Finset ι)
    (length count : ι → ℕ) (ell c : ℕ)
    (hpart : ∀ i ∈ parts, 2 * count i ≤ length i + 2 * c)
    (hbudget : (∑ i ∈ parts, length i) + 2 * c * parts.card ≤ ell + 2 * c) :
    2 * (∑ i ∈ parts, count i) ≤ ell + 2 * c := by
  calc
    2 * (∑ i ∈ parts, count i) = ∑ i ∈ parts, 2 * count i :=
      Finset.mul_sum ..
    _ ≤ ∑ i ∈ parts, (length i + 2 * c) := Finset.sum_le_sum hpart
    _ = (∑ i ∈ parts, length i) + 2 * c * parts.card := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ ell + 2 * c := hbudget

end RootedKP.EndpointCounting
