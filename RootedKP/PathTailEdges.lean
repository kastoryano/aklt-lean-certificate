import RootedKP.PathEdgeSplit
import RootedKP.PathTails
import RootedKP.LoopOverlap

/-! Complete lengthwise path counts on specified regional edges. -/
namespace RootedKP.AKLT
open Honeycomb RegionalEndpoints
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

lemma polymer_eq_of_path_edges {F : Rectangle} (p q : Polymer F)
    (hp : p.kind = .path) (hq : q.kind = .path) (he : p.edges = q.edges) : p = q := by
  cases p
  cases q
  simp only at hp hq he
  cases hp
  cases hq
  cases he
  rfl

def pathsOnEdge (F : Rectangle) (e : Edge) (n : ℕ) : Finset (Polymer F) :=
  Finset.univ.filter (fun q => q.kind = .path ∧ e ∈ q.edges ∧ q.length = n)

lemma pathsOnEdge_image_card (F : Rectangle) (e : Edge) (n : ℕ) :
    ((pathsOnEdge F e n).image Polymer.edges).card = (pathsOnEdge F e n).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  exact polymer_eq_of_path_edges p q (Finset.mem_filter.mp hp).2.1
    (Finset.mem_filter.mp hq).2.1 he

lemma pathsOnEdge_image_realizes (F : Rectangle) (u v : Vertex) (n : ℕ)
    (e : Finset Edge) (he : e ∈ (pathsOnEdge F s(u,v) n).image Polymer.edges) :
    ∃ p : BoundaryPath F 200, p.length = n ∧ pathEdges p = e ∧ s(u,v) ∈ e := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨hk,hedge,hlen⟩ := (Finset.mem_filter.mp hq).2
  have hr := q.realization
  rw [hk] at hr
  obtain ⟨p,hp⟩ := hr
  exact ⟨p,(q.length_of_path_realization p hp).symm.trans hlen,hp,hedge⟩

lemma pathsOnEdge_core_bound (F : Rectangle) (n : ℕ) (hn : 21 ≤ n)
    (u v : Vertex) (hadj : SunAdj F 200 u v)
    (hu : Core F 200 u) (hv : Core F 200 v) :
    ((pathsOnEdge F s(u,v) n).card : ℝ) ≤ (2*(n:ℝ)+95)*2^n/1024 := by
  have h := interior_edge_family_convolution F n hn u v hadj hu hv
    ((pathsOnEdge F s(u,v) n).image Polymer.edges) (pathsOnEdge_image_realizes F u v n)
  rw [pathsOnEdge_image_card] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  norm_num only [Rat.cast_natCast,Rat.cast_div,Rat.cast_mul,Rat.cast_add,
    Rat.cast_ofNat,Rat.cast_pow] at h'
  exact h'

lemma pathsOnEdge_leaf_bound (F : Rectangle) (n : ℕ) (hn : 21 ≤ n)
    (u v : Vertex) (hadj : SunAdj F 200 u v)
    (hu : Leaf F 200 u) (hv : Core F 200 v) :
    ((pathsOnEdge F s(u,v) n).card : ℝ) ≤ 2^n/32 := by
  have h := boundary_edge_family_long F n (by omega) u v hadj hu hv
    ((pathsOnEdge F s(u,v) n).image Polymer.edges) (pathsOnEdge_image_realizes F u v n)
  rw [pathsOnEdge_image_card] at h
  have hp : (2:ℝ)^n = 2^(n-5)*32 := by
    rw [show (32:ℝ) = 2^5 by norm_num]
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ (2:ℝ)^(n-5) := by exact_mod_cast h
    _ = _ := by rw [hp]; ring

lemma pathsOnEligibleEdge_bound {F : Rectangle} (p : Polymer F) (n : ℕ)
    (hn : 21 ≤ n) (e : Edge) (he : e ∈ p.eligibleEdges) :
    ((pathsOnEdge F e n).card : ℝ) ≤ (2*(n:ℝ)+95)*2^n/1024 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    obtain ⟨he,hcore⟩ := (p.mem_eligibleEdges _).mp he
    exact pathsOnEdge_core_bound F n hn u v (p.edge_sunAdj he)
      (hcore u (Sym2.mem_mk_left ..)) (hcore v (Sym2.mem_mk_right ..))

lemma pathsOnNoneligibleEdge_bound {F : Rectangle} (p : Polymer F) (n : ℕ)
    (hn : 21 ≤ n) (e : Edge) (he : e ∈ p.edges \ p.eligibleEdges) :
    ((pathsOnEdge F e n).card : ℝ) ≤ 2^n/32 := by
  obtain ⟨he,hne⟩ := Finset.mem_sdiff.mp he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hadj := p.edge_sunAdj he
    by_cases hu : Core F 200 u
    · have hv : ¬ Core F 200 v := by
        intro hv
        apply hne ((p.mem_eligibleEdges _).mpr ⟨he,?_⟩)
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hu
        · exact hv
      have hleaf := noncore_sun_vertex_is_leaf ⟨u,sunAdj_symm hadj⟩ hv
      simpa only [Sym2.eq_swap] using pathsOnEdge_leaf_bound F n hn v u
        (sunAdj_symm hadj) hleaf hu
    · have hv : Core F 200 v := hadj.2.resolve_left hu
      exact pathsOnEdge_leaf_bound F n hn u v hadj
        (noncore_sun_vertex_is_leaf ⟨v,hadj⟩ hu) hv

/-- A shared-edge cover reduces all incompatible path counts to the two
verified local endpoint estimates. -/
theorem path_length_count_le_edge_charges {F : Rectangle} (p : Polymer F)
    (n : ℕ) (hn : 21 ≤ n)
    (hcover : ∀ q ∈ (tailPathSet p).filter (fun q => q.length = n),
      ∃ e ∈ p.edges, e ∈ q.edges) :
    ((((tailPathSet p).filter fun q => q.length = n).card : ℝ)) ≤
      (p.eligibleEdges.card : ℝ) * ((2*(n:ℝ)+95)*2^n/1024) +
      ((p.edges \ p.eligibleEdges).card : ℝ) * (2^n/32) := by
  have hsub : (tailPathSet p).filter (fun q => q.length = n) ⊆
      p.edges.biUnion (fun e => pathsOnEdge F e n) := by
    intro q hq
    obtain ⟨e,he,hqe⟩ := hcover q hq
    have hq' := Finset.mem_filter.mp hq
    have hkind := (Finset.mem_filter.mp (Finset.mem_filter.mp hq'.1).1).2.1
    exact Finset.mem_biUnion.mpr ⟨e,he,by simp [pathsOnEdge,hkind,hqe,hq'.2]⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcast : ((((tailPathSet p).filter fun q => q.length = n).card : ℝ)) ≤
      ∑ e ∈ p.edges, ((pathsOnEdge F e n).card : ℝ) := by exact_mod_cast hcard
  apply hcast.trans
  have hsplit : (∑ e ∈ p.edges, ((pathsOnEdge F e n).card : ℝ)) =
      (∑ e ∈ p.eligibleEdges, ((pathsOnEdge F e n).card : ℝ)) +
      ∑ e ∈ p.edges \ p.eligibleEdges, ((pathsOnEdge F e n).card : ℝ) := by
    simpa only [add_comm] using (Finset.sum_sdiff (f := fun e =>
      ((pathsOnEdge F e n).card : ℝ)) p.eligibleEdges_subset).symm
  rw [hsplit]
  apply add_le_add
  · calc
      _ ≤ ∑ _e ∈ p.eligibleEdges, (2*(n:ℝ)+95)*2^n/1024 :=
        Finset.sum_le_sum (fun e he => pathsOnEligibleEdge_bound p n hn e he)
      _ = _ := by simp
  · calc
      _ ≤ ∑ _e ∈ p.edges \ p.eligibleEdges, (2:ℝ)^n/32 :=
        Finset.sum_le_sum (fun e he => pathsOnNoneligibleEdge_bound p n hn e he)
      _ = _ := by simp

end
end RootedKP.AKLT
#print axioms RootedKP.AKLT.pathsOnEdge_core_bound
#print axioms RootedKP.AKLT.pathsOnEdge_leaf_bound
#print axioms RootedKP.AKLT.path_length_count_le_edge_charges
