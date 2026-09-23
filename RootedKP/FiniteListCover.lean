import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace RootedKP
open scoped BigOperators

theorem card_le_list_sum_of_cover {α β : Type*} [DecidableEq α]
    (S : Finset α) (pieces : List β) (f : β → Finset α)
    (hcover : ∀ x ∈ S, ∃ b ∈ pieces, x ∈ f b) :
    S.card ≤ (pieces.map (fun b => (f b).card)).sum := by
  induction pieces generalizing S with
  | nil =>
    have : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨b,hb,_⟩ := hcover x hx
      cases hb
    simp [this]
  | cons b bs ih =>
    have hrest : ∀ x ∈ S \ f b, ∃ c ∈ bs, x ∈ f c := by
      intro x hx
      obtain ⟨hxS,hxb⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨c,hc,hxc⟩ := hcover x hxS
      rcases List.mem_cons.mp hc with rfl | hc
      · exact False.elim (hxb hxc)
      · exact ⟨c,hc,hxc⟩
    have hh := ih (S \ f b) hrest
    have hsub : S ⊆ f b ∪ (S \ f b) := by
      intro x hx
      by_cases h : x ∈ f b
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,h⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simpa using hc.trans (Nat.add_le_add_left hh (f b).card)

end RootedKP
