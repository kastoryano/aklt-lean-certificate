import RootedKP.CircleArcs
import RootedKP.BoundaryCandidateCount

namespace RootedKP.Honeycomb.BoundaryLeaves
open BoundaryCycle CircleArcs
set_option maxHeartbeats 0

/-- Even if a padded trace covers the whole circle, the literal candidates
still have density at most one half around the complete outer boundary. -/
theorem total_candidate_count (F : Rectangle) (s : Finset (Fin 6 × ℤ))
    (hc : ∀ a ∈ s, Candidate F a.1 a.2) :
    2 * (s.card : ℤ) ≤ perimeter F 0 := by
  classical
  let f : Fin 6 × ℤ → ℤ := fun a => coordinate F 0 a.1 (2*a.2+1)
  have hp := perimeter_positive F (by decide : 0 ≤ 4)
  have hspace : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 2 ≤ |f a-f b| := by
    intro a ha b hb hne
    have hh := candidate_coordinate_spacing (hc a ha) (hc b hb) hne
    change (f a+2 ≤ f b ∧ _) ∨ (f b+2 ≤ f a ∧ _) at hh
    rcases hh with hh | hh
    · rw [abs_of_nonpos (by omega)]
      omega
    · rw [abs_of_nonneg (by omega)]
      omega
  have hinj : Set.InjOn f (s : Set (Fin 6 × ℤ)) := by
    intro a ha b hb heq
    by_contra hne
    have hh := hspace a ha b hb hne
    rw [heq,sub_self,abs_zero] at hh
    omega
  have hrange : ∀ x ∈ s.image f, 0 ≤ x ∧ x ≤ perimeter F 0 - 1 := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hv := parameter_valid (candidate_valid (hc a ha))
    have hh := coordinate_range F (by decide : 0 ≤ 4) a.1 hv.1 hv.2
    change 0 ≤ f a ∧ f a < perimeter F 0 at hh
    omega
  have hs : ∀ x ∈ s.image f, ∀ y ∈ s.image f, x ≠ y → 2 ≤ |x-y| := by
    intro x hx y hy hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    exact hspace a ha b hb (fun h => hne (congrArg f h))
  have hh := RootedKP.EndpointCounting.two_spaced_card (s.image f) 0
    (perimeter F 0-1) (by omega) hrange hs
  rw [Finset.card_image_of_injOn hinj] at hh
  have hq := F.q_order
  have hr := F.r_order
  dsimp only [perimeter,baseLength,width,height] at hp hh ⊢
  omega

def imageCoordinate (F : Rectangle) (d : ℕ) (a : Fin 6 × ℤ) : ℤ :=
  coordinate F d a.1 (clamp (lower F d a.1) (upper F a.1) (2*a.2+1))

/-- Clamping allows either endpoint of a side interval, so the same cyclic
joint can have the closed-coordinate representatives zero and perimeter. -/
theorem imageCoordinate_range (F : Rectangle) {d : ℕ} (hd : d ≤ 4)
    (a : Fin 6 × ℤ) : 0 ≤ imageCoordinate F d a ∧ imageCoordinate F d a ≤ perimeter F d := by
  obtain ⟨i,r⟩ := a
  have hq := F.q_order
  have hr := F.r_order
  fin_cases i <;>
    simp only [imageCoordinate,coordinate,offset,perimeter,baseLength,width,height,
      lower,upper,sideChart,clamp,max_def,min_def] <;>
    split_ifs <;> omega

/-- A root trace and contacts within n−2 steps give the actual candidate
bound. Both the short-arc and full-circle cases are covered. -/
theorem candidates_near_trace (F : Rectangle) {d n L : ℕ} (hd : d ≤ 4) (hn : 2 ≤ n)
    (xs : List ℤ) (htrace : Trace (perimeter F d) xs)
    (hlen : xs.length-1 ≤ L) (s : Finset (Fin 6 × ℤ))
    (hc : ∀ a ∈ s, Candidate F a.1 a.2)
    (hcontact : ∀ a ∈ s, ∃ x ∈ xs,
      Near (perimeter F d) (n-2 : ℕ) x (imageCoordinate F d a)) :
    2 * s.card ≤ L + 2*(n-1+6*d) := by
  have hp := perimeter_positive F hd
  by_cases hfull : perimeter F d ≤ (L : ℤ) + 2*(n-2 : ℕ)
  · have ht := total_candidate_count F s hc
    have hper := perimeter_loss F d
    omega
  · have hshort : (xs.length-1 : ℕ) + 2*(n-2 : ℕ) < perimeter F d := by omega
    obtain ⟨cut,lo,hi,hcut0,hcutP,horder,hwidth,harc⟩ :=
      trace_contacts_arc hp (Int.natCast_nonneg (n-2)) htrace hshort
    apply candidates_over_padded_arc F hd cut lo hi horder s L n hn hc
    · intro a ha
      have hb := imageCoordinate_range F hd a
      exact harc (imageCoordinate F d a) hb.1 hb.2 (hcontact a ha)
    · omega

end RootedKP.Honeycomb.BoundaryLeaves
