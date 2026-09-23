import RootedKP.BoundaryLeaves
import RootedKP.BoundaryArcPreimage
import RootedKP.EndpointCounting
import Mathlib.Data.Finset.Max

namespace RootedKP.Honeycomb.BoundaryLeaves
open BoundaryCycle

/-- Candidate spacing survives unwrapping at any image-circle cut. -/
theorem candidate_lift_spacing {F : Rectangle} {d : ℕ} (cut : ℤ)
    {i j : Fin 6} {r s : ℤ} (hi : Candidate F i r) (hj : Candidate F j s)
    (hne : (i,r) ≠ (j,s)) :
    2 ≤ |liftOuter F d cut i (2*r+1) - liftOuter F d cut j (2*s+1)| := by
  have hh := candidate_coordinate_spacing hi hj hne
  have hp := perimeter_positive F (by decide : 0 ≤ 4)
  dsimp only at hh
  by_contra h
  have ha := abs_lt.mp (lt_of_not_ge h)
  unfold liftOuter at ha
  split_ifs at ha <;> omega

/-- Actual candidate attachment cores over any inner arc satisfy the
required half-density bound, including wrapping arcs and collapsed fibers. -/
theorem candidates_over_arc (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (cut lo hi : ℤ) (horder : lo ≤ hi) (s : Finset (Fin 6 × ℤ))
    (hc : ∀ a ∈ s, Candidate F a.1 a.2)
    (himage : ∀ a ∈ s,
      lo ≤ liftImage F d cut a.1 (2*a.2+1) ∧ liftImage F d cut a.1 (2*a.2+1) ≤ hi) :
    2 * s.card ≤ (hi - lo + 12*d).toNat + 2 := by
  classical
  let f : Fin 6 × ℤ → ℤ := fun a => liftOuter F d cut a.1 (2*a.2+1)
  have hs : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 2 ≤ |f a - f b| := by
    intro a ha b hb hne
    exact candidate_lift_spacing cut (hc a ha) (hc b hb) hne
  have hinj : Set.InjOn f (s : Set (Fin 6 × ℤ)) := by
    intro a ha b hb heq
    by_contra hne
    have hh := hs a ha b hb hne
    rw [heq, sub_self, abs_zero] at hh
    omega
  let t := s.image f
  by_cases ht : t.Nonempty
  · let a := t.min' ht
    have ha : a ∈ t := Finset.min'_mem t ht
    obtain ⟨b, hb, hfb⟩ := Finset.mem_image.mp ha
    have hbvalid := parameter_valid (candidate_valid (hc b hb))
    have hrange : ∀ x ∈ t, a ≤ x ∧ x ≤ a + (hi-lo+12*d) := by
      intro x hx
      obtain ⟨c, hc', hfc⟩ := Finset.mem_image.mp hx
      have hcvalid := parameter_valid (candidate_valid (hc c hc'))
      have hlen := arc_preimage_extent F hd cut lo hi c.1 b.1 (2*c.2+1) (2*b.2+1)
        hcvalid.1 hcvalid.2 hbvalid.1 hbvalid.2 (himage c hc').2 (himage b hb).1
      change f c - f b ≤ hi-lo+12*d at hlen
      constructor
      · exact Finset.min'_le t x hx
      · omega
    have htspace : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 2 ≤ |x-y| := by
      intro x hx y hy hne
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hy
      apply hs b hb c hc'
      intro heq
      exact hne (congrArg f heq)
    have hh := RootedKP.EndpointCounting.two_spaced_card t a (a+(hi-lo+12*d))
      (by omega) hrange htspace
    have hcard : t.card = s.card := Finset.card_image_of_injOn hinj
    rw [hcard] at hh
    have heq : a+(hi-lo+12*d)-a = hi-lo+12*d := by omega
    simpa only [heq] using hh
  · have ht' : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hc' : t.card = s.card := Finset.card_image_of_injOn hinj
    rw [ht', Finset.card_empty] at hc'
    omega

/-- The paper's endpoint coefficient follows for an image arc enlarged by
`n-2` at each end. This statement counts actual leaf-row candidates. -/
theorem candidates_over_padded_arc (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (cut lo hi : ℤ) (horder : lo ≤ hi) (s : Finset (Fin 6 × ℤ)) (L n : ℕ)
    (hn : 2 ≤ n) (hc : ∀ a ∈ s, Candidate F a.1 a.2)
    (himage : ∀ a ∈ s,
      lo ≤ liftImage F d cut a.1 (2*a.2+1) ∧ liftImage F d cut a.1 (2*a.2+1) ≤ hi)
    (hlen : hi-lo ≤ (L : ℤ) + 2*(n-2 : ℕ)) :
    2 * s.card ≤ L + 2*(n-1+6*d) := by
  have hh := candidates_over_arc F hd cut lo hi horder s hc himage
  omega

end RootedKP.Honeycomb.BoundaryLeaves
