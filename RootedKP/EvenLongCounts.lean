import RootedKP.PieceEndpointCount
import RootedKP.RegionalSideCounting
import RootedKP.PathTailEdges
import RootedKP.FiniteListCover

/-! Actual even boundary-path counts for arbitrary canonical roots. The
ring-piece budget and per-endpoint R(n) count are both discharged here. -/
namespace RootedKP.AKLT
open Honeycomb BoundaryCounts
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

theorem fixed_right_endpoint_card {F : Rectangle} (n : ℕ) (a : Fin 6 × ℤ)
    (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n ∧ q.RightEndpoint a) :
    T.card ≤ sideCount n := by
  have hinj : Set.InjOn Polymer.edges (T : Set (Polymer F)) := by
    intro p hp q hq he
    exact polymer_eq_of_path_edges p q (hT p hp).1 (hT q hq).1 he
  rw [← Finset.card_image_of_injOn hinj]
  apply RegionalSide.edge_family_card_le F n a.1 a.2
  intro e he
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hk,hlen,hcan,r,hr,t,ht,hts,hends⟩ := hT q hq
  exact ⟨r,(q.length_of_path_realization r hr).symm.trans hlen,hr,t,hts,hends⟩

theorem family_card_le_endpoint_card_mul {F : Rectangle} {n : ℕ}
    (hmax : n≤20) (heven : n%2=0) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n) :
    T.card ≤ (T.image Polymer.rightEndpoint).card * sideCount n := by
  have hfilter : T.filter (fun q => q.rightEndpoint ∈ T.image Polymer.rightEndpoint) = T := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
  have hsum := Finset.sum_card_fiberwise_eq_card_filter T
    (T.image Polymer.rightEndpoint) Polymer.rightEndpoint
  rw [hfilter] at hsum
  rw [← hsum]
  calc
    _ ≤ ∑ _a ∈ T.image Polymer.rightEndpoint, sideCount n := by
      apply Finset.sum_le_sum
      intro a ha
      apply fixed_right_endpoint_card n a
      intro q hq
      obtain ⟨hqT,hqa⟩ := Finset.mem_filter.mp hq
      obtain ⟨hk,hn⟩ := hT q hqT
      exact ⟨hk,hn,hqa ▸ q.rightEndpoint_spec hk (by omega) (by omega)⟩
    _ = _ := by simp

theorem even_root_endpoint_count {F : Rectangle} (p : Polymer F) {n : ℕ}
    (hmin : 8≤n) (hmax : n≤20) (heven : n%2=0) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) :
    2*(T.image Polymer.rightEndpoint).card ≤ p.length+2*(n-1+6*(n/4-1)) := by
  obtain ⟨parts,hbudget,hcover⟩ := p.short_even_ring_cover n hmin hmax heven
  let f : TracePiece (Ring F (n/4-1)) → Finset (Fin 6 × ℤ) := fun piece =>
    (T.filter (fun q => ¬Disjoint piece.support q.support)).image Polymer.rightEndpoint
  have hcov : ∀ a ∈ T.image Polymer.rightEndpoint, ∃ piece ∈ parts, a ∈ f piece := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hk,hn,hi⟩ := hT q hq
    obtain ⟨piece,hpiece,hmeet⟩ := hcover q hk hn hi
    exact ⟨piece,hpiece,Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hmeet⟩,rfl⟩⟩
  have hc := card_le_list_sum_of_cover _ parts f hcov
  have hpart : ∀ piece, 2*(f piece).card ≤ piece.length+2*(n-1+6*(n/4-1)) := by
    intro piece
    apply Polymer.piece_endpoint_count hmin hmax heven
    intro q hq
    obtain ⟨hqT,hmeet⟩ := Finset.mem_filter.mp hq
    exact ⟨(hT q hqT).1,(hT q hqT).2.1,hmeet⟩
  have hsum : 2*(parts.map (fun piece => (f piece).card)).sum ≤
      (parts.map TracePiece.length).sum + 2*(n-1+6*(n/4-1))*parts.length := by
    clear hc hcov hcover hbudget
    induction parts with
    | nil => simp
    | cons piece rest ih =>
      have hp := hpart piece
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Nat.add_le_add hp ih
  exact (Nat.mul_le_mul_left 2 hc).trans (hsum.trans hbudget)

/-- The paper's collar estimate, on the actual unoriented polymer family. -/
theorem even_root_family_count {F : Rectangle} (p : Polymer F) {n : ℕ}
    (hmin : 8≤n) (hmax : n≤20) (heven : n%2=0) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T, q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) :
    2*T.card ≤ (p.length+2*(n-1+6*(n/4-1)))*sideCount n := by
  have hc := family_card_le_endpoint_card_mul hmax heven T
    (fun q hq => ⟨(hT q hq).1,(hT q hq).2.1⟩)
  have he := even_root_endpoint_count p hmin hmax heven T hT
  calc
    2*T.card ≤ 2*((T.image Polymer.rightEndpoint).card*sideCount n) := Nat.mul_le_mul_left 2 hc
    _ = (2*(T.image Polymer.rightEndpoint).card)*sideCount n := (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ he

end
end RootedKP.AKLT
