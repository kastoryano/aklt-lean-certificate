import RootedKP.RegionalSideCounting
import RootedKP.PieceEndpointCount

/-! Literal canonical short even paths, grouped by their actual right leaf.
The per-leaf R(n) count is proved from a global side-chart embedding. -/
namespace RootedKP.AKLT
open Honeycomb BoundaryCounts
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

lemma same_kind_edges_injective {F : Rectangle} (T : Finset (Polymer F))
    (hk : ∀p∈T,p.kind=.path) : Set.InjOn Polymer.edges (↑T : Set (Polymer F)) := by
  intro p hp q hq he
  have hp' := hk p hp
  have hq' := hk q hq
  cases p
  cases q
  simp only at hp' hq' he
  cases hp'
  cases hq'
  cases he
  rfl

/-- Per-right-leaf bound for finite families of actual canonical polymers. -/
theorem right_endpoint_family_card_le (F : Rectangle) (n : ℕ)
    (a : Fin 6 × ℤ) (T : Finset (Polymer F))
    (hT : ∀p∈T,p.kind=.path ∧ p.length=n ∧ p.RightEndpoint a) :
    T.card ≤ sideCount n := by
  have hi := same_kind_edges_injective T (fun p hp => (hT p hp).1)
  rw [← Finset.card_image_iff.mpr hi]
  apply RegionalSide.edge_family_card_le F n a.1 a.2 (T.image Polymer.edges)
  intro e he
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hk,hlen,hcan,r,hr,t,ht,hts,hends⟩ := hT p hp
  exact ⟨r,(p.length_of_path_realization r hr).symm.trans hlen,hr,t,hts,hends⟩

/-- The canonical endpoint chosen by geometry satisfies the same R(n) bound. -/
theorem chosen_endpoint_family_card_le (F : Rectangle) (n : ℕ)
    (hn : n≤20) (heven : n%2=0) (a : Fin 6 × ℤ) (T : Finset (Polymer F))
    (hT : ∀p∈T,p.kind=.path ∧ p.length=n ∧ p.rightEndpoint=a) :
    T.card ≤ sideCount n := by
  apply right_endpoint_family_card_le F n a T
  intro p hp
  obtain ⟨hk,hlen,ha⟩ := hT p hp
  refine ⟨hk,hlen,?_⟩
  simpa only [ha] using p.rightEndpoint_spec hk (by omega) (by omega)

lemma sideCount_eq_arithmetic (n : ℕ) (hlo : 8≤n) (hhi : n≤20) (heven : n%2=0) :
    sideCount n = Arithmetic.evenCountsFrom8[(n-8)/2]! := by
  let k : Fin 9 := ⟨(n-4)/2,by omega⟩
  have hn : 2*k.val+4=n := by dsimp [k]; omega
  have h := sideCount_at k
  rw [hn] at h
  rw [h]
  interval_cases n <;> norm_num [k,Arithmetic.evenCountsFrom8] at heven ⊢

theorem chosen_endpoint_family_R_bound (F : Rectangle) (n : ℕ)
    (hlo : 8≤n) (hhi : n≤20) (heven : n%2=0) (a : Fin 6 × ℤ)
    (T : Finset (Polymer F))
    (hT : ∀p∈T,p.kind=.path ∧ p.length=n ∧ p.rightEndpoint=a) :
    T.card ≤ Arithmetic.evenCountsFrom8[(n-8)/2]! := by
  rw [← sideCount_eq_arithmetic n hlo hhi heven]
  exact chosen_endpoint_family_card_le F n hhi heven a T hT

end
end RootedKP.AKLT
#print axioms RootedKP.AKLT.chosen_endpoint_family_R_bound
