import RootedKP.RemainingCounts
import RootedKP.CatalogStartPruning

/-! Only the cumulative prefix through length fourteen needs enumeration.
The already proved geometry supplies a conservative common suffix. -/
namespace RootedKP.AKLT
open Honeycomb Arithmetic BoundaryCounts ShortRootRepresentatives
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def geometricSuffix : List ℕ := [647,7740,2094,24662,6803,89378]
def hybridCounts (cs : List ℕ) : List ℕ := cs.take 12 ++ geometricSuffix

def ShortPrefixBound {F : Rectangle} (p : Polymer F) (cs : List ℕ) : Prop :=
  ∀k ≤ 12,prefixSum (fun i => (pathLengthCount p i : ℝ)) k ≤ 
    prefixSum (fun i => (cs[i]?.getD 0 : ℝ)) k

structure ShortPrefixCatalogBounds : Prop where
  paths : ∀ell : Fin 3,∀root∈boundaryRootTrails (4+ell.val),∀k : Fin 13,
    (∑i∈Finset.range k.val,catalogCount root.toFinset (3+i)) ≤ 
    ∑i∈Finset.range k.val,(shortCounts (4+ell.val))[i]?.getD 0
  loops : ∀entry∈loopRootTrails,∀k : Fin 13,
    (∑i∈Finset.range k.val,catalogCount entry.2.toFinset (3+i)) ≤ 
    ∑i∈Finset.range k.val,L6Counts[i]?.getD 0

theorem short_geometric_suffix {F : Rectangle} (p : Polymer F) (hp : p.length ≤ 6)
    (i : ℕ) (hi : 12 ≤ i) (hi' : i < 18) :
    pathLengthCount p i ≤ geometricSuffix[i-12]?.getD 0 := by
  interval_cases i
  · have hh := odd_small_root_family_count p (by omega) (show 15 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=15)) (counted_path_spec p 12)
    simpa [pathLengthCount,Q15,geometricSuffix] using hh
  · have hh := even_root_family_count p (show 8 ≤ 16 by omega) (show 16 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=16)) (counted_path_spec p 13)
    norm_num [R16] at hh
    change pathLengthCount p 13 ≤ 7740
    norm_num [pathLengthCount]
    omega
  · have hh := odd_small_root_family_count p (by omega) (show 17 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=17)) (counted_path_spec p 14)
    simpa [pathLengthCount,Q17,geometricSuffix] using hh
  · have hh := even_root_family_count p (show 8 ≤ 18 by omega) (show 18 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=18)) (counted_path_spec p 15)
    norm_num [R18] at hh
    change pathLengthCount p 15 ≤ 24662
    norm_num [pathLengthCount]
    omega
  · have hh := odd_small_root_family_count p (by omega) (show 19 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=19)) (counted_path_spec p 16)
    simpa [pathLengthCount,Q19,geometricSuffix] using hh
  · have hh := even_root_family_count p (show 8 ≤ 20 by omega) (show 20 ≤ 20 by omega) (by decide)
      ((shortPathSet p).filter (fun q => q.length=20)) (counted_path_spec p 17)
    norm_num [R20] at hh
    change pathLengthCount p 17 ≤ 89378
    norm_num [pathLengthCount]
    omega

theorem hybrid_lookup_low (cs : List ℕ) (hlen : cs.length=18) {i : ℕ} (hi : i < 12) :
    (hybridCounts cs)[i]?=cs[i]? := by
  simp [hybridCounts,List.getElem?_append,List.getElem?_take,hlen,hi]

theorem hybrid_lookup_high (cs : List ℕ) (hlen : cs.length=18) {i : ℕ} (hi : 12 ≤ i) :
    (hybridCounts cs)[i]?=geometricSuffix[i-12]? := by
  simp [hybridCounts,List.getElem?_append,hlen,show ¬i < 12 by omega]

theorem hybrid_cumulative_of_prefix {F : Rectangle} (p : Polymer F) (hp : p.length ≤ 6)
    (cs : List ℕ) (hlen : cs.length=18) (hc : ShortPrefixBound p cs) :
    CumulativePathBound p (hybridCounts cs) := by
  refine ⟨by simp [hybridCounts,geometricSuffix,hlen],?_⟩
  intro k hk
  have hlow : ∀m ≤ 12,prefixSum (fun i => (pathLengthCount p i : ℝ)) m ≤ 
      prefixSum (fun i => ((hybridCounts cs)[i]?.getD 0 : ℝ)) m := by
    intro m hm
    convert hc m hm using 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hybrid_lookup_low cs hlen (i:=i) (by have := Finset.mem_range.mp hi; omega)]
  by_cases hsmall : k ≤ 12
  · exact hlow k hsmall
  · have heq : k=12+(k-12) := by omega
    unfold prefixSum
    rw [heq,Finset.sum_range_add,Finset.sum_range_add]
    apply add_le_add (hlow 12 le_rfl)
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [hybrid_lookup_high cs hlen (i:=12+j) (by omega)]
    exact_mod_cast short_geometric_suffix p hp (12+j) (by omega) (by omega)

def hybridShortAllowance {F : Rectangle} (p : Polymer F) : ℚ :=
  pathFactor*(sumCounts weightCap 3 1
    (hybridCounts (if p.kind=.path then shortCounts p.length else L6Counts))+
    tailEnvelopeAllowance p)

theorem hybrid_allowance_le_cost {F : Rectangle} (p : Polymer F) (hp : p.length ≤ 6) :
    hybridShortAllowance p+loopAllowance p ≤ a p.length := by
  cases hk : p.kind with
  | path =>
    have hmin := p.length_ge_three
    have hs : p.length=3 ∨ p.length=4 ∨ p.length=5 ∨ p.length=6 := by omega
    rcases hs with h | h | h | h <;>
      norm_num [hybridShortAllowance,hybridCounts,geometricSuffix,tailEnvelopeAllowance,
        loopAllowance,hk,h,shortCounts,W3Counts,W4Counts,W5Counts,W6Counts,a,pathFactor,
        sumCounts,weightCap,rCap,qCap,boundaryTail,interiorTail,tail0,tail1,loopMass,loopCounts]
  | loop =>
    have h : p.length=6 := by have := p.loop_length_ge_six hk; omega
    norm_num [hybridShortAllowance,hybridCounts,geometricSuffix,tailEnvelopeAllowance,
      loopAllowance,hk,h,L6Counts,a,pathFactor,sumCounts,weightCap,rCap,qCap,
      boundaryTail,interiorTail,tail0,tail1,loopMass,loopCounts]

theorem prefix_of_catalog_family {F : Rectangle} (p : Polymer F)
    (root : Finset Vertex) (cs : List ℕ)
    (hc : ∀k : Fin 13,(∑i∈Finset.range k.val,catalogCount root (3+i)) ≤ 
      ∑i∈Finset.range k.val,cs[i]?.getD 0)
    (hfamily : ∀n ≤ 20,∀T : Finset (Polymer F),
      (∀q∈T,q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) →
      T.card ≤ catalogCount root n) : ShortPrefixBound p cs := by
  intro k hk
  have hb := hc ⟨k,by omega⟩
  have hh : (∑i∈Finset.range k,pathLengthCount p i) ≤ 
      ∑i∈Finset.range k,catalogCount root (3+i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply hfamily (3+i) (by have := Finset.mem_range.mp hi; omega)
      ((shortPathSet p).filter (fun q => q.length=3+i)) (counted_path_spec p i)
  have hnat := hh.trans hb
  unfold prefixSum
  simp only
  exact_mod_cast hnat

theorem short_prefix_of_catalog (H : ShortPrefixCatalogBounds)
    {F : Rectangle} (p : Polymer F) (hp : p.length ≤ 6) :
    ShortPrefixBound p (if p.kind=.path then shortCounts p.length else L6Counts) := by
  cases hk : p.kind with
  | path =>
    simp only [hk,ite_true]
    by_cases h3 : p.length=3
    · intro k hk
      simpa [h3,shortCounts] using (three_root_cumulative p h3).2 k (by omega)
    · have hmin : 4 ≤ p.length := by have := p.length_ge_three; omega
      obtain ⟨root,hr,hfamily⟩ := short_path_root_catalog p hk hp
      have heq : 4+(p.length-4)=p.length := by omega
      have hc := H.paths ⟨p.length-4,by omega⟩
      simp only [heq] at hc
      exact prefix_of_catalog_family p root.toFinset (shortCounts p.length) (hc root hr) hfamily
  | loop =>
    simp only [hk,show Kind.loop≠Kind.path by decide,ite_false]
    obtain ⟨entry,hr,hfamily⟩ := short_loop_root_catalog p hk hp
    exact prefix_of_catalog_family p entry.2.toFinset L6Counts (H.loops entry hr) hfamily

theorem short_counts_length {F : Rectangle} (p : Polymer F) (hp : p.length ≤ 6) :
    (if p.kind=.path then shortCounts p.length else L6Counts).length=18 := by
  split_ifs with hk
  · have hmin := p.length_ge_three
    have hs : p.length=3 ∨ p.length=4 ∨ p.length=5 ∨ p.length=6 := by omega
    rcases hs with h | h | h | h <;> simp [shortCounts,h,W3Counts,W4Counts,W5Counts,W6Counts]
  · rfl

/-- The complete KP implication with finite checks only through length fourteen.
The short-root numerical premise and the length-four premise remain explicit. -/
theorem uniformKP_of_prefix_catalog_and_four (HC : ShortPrefixCatalogBounds)
    (H4 : FourPathCountBound) : UniformKPCondition := by
  intro F p
  have hreal : (∑q∈Finset.univ.filter (fun q => Polymer.Incompatible q p),realBudget q) ≤ p.cost := by
    rw [incompatible_sum_eq_kind_masses,cost_eq_arithmetic]
    have hloop := loop_kindMass_le_allowance F p
    have ht := regional_path_tail_bound F p
    by_cases hp : p.length ≤ 6
    · have hc := hybrid_cumulative_of_prefix p hp _ (short_counts_length p hp)
        (short_prefix_of_catalog HC p hp)
      have hs := short_envelope_le_of_cumulative p _ hc
      have hpath := (kind_path_mass_le_envelopes p).trans
        (mul_le_mul_of_nonneg_left (add_le_add hs ht) (by norm_num : (0:ℝ) ≤ 5/6))
      have heq : (5/6:ℝ)*((sumCounts weightCap 3 1
          (hybridCounts (if p.kind=.path then shortCounts p.length else L6Counts)) : ℝ)+
          (tailEnvelopeAllowance p : ℝ))=(hybridShortAllowance p : ℝ) := by
        simp [hybridShortAllowance,pathFactor]
      rw [heq] at hpath
      have hcost : ((hybridShortAllowance p+loopAllowance p : ℚ) : ℝ) ≤ (a p.length : ℝ) := by
        exact_mod_cast hybrid_allowance_le_cost p hp
      push_cast at hcost
      exact (add_le_add hpath hloop).trans hcost
    · have hs := long_envelope_of_length_counts (long_length_count_bound_of_four H4) F p (by omega)
      have hpath := (kind_path_mass_le_envelopes p).trans
        (mul_le_mul_of_nonneg_left (add_le_add hs ht) (by norm_num : (0:ℝ) ≤ 5/6))
      have heq : (5/6:ℝ)*((longFiniteUniformAllowance p.length : ℝ)+
          (tailEnvelopeAllowance p : ℝ))=(pathAllowance p : ℝ) := by
        simp [tailEnvelopeAllowance,pathAllowance,hp,pathFactor]
      rw [heq] at hpath
      have hcost : ((pathAllowance p+loopAllowance p : ℚ) : ℝ) ≤ (a p.length : ℝ) := by
        exact_mod_cast allowance_le_cost p
      push_cast at hcost
      exact (add_le_add hpath hloop).trans hcost
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => realBudget_nonneg q)] at h
  rw [tsum_fintype]
  simpa only [Finset.sum_filter,realBudget,ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal] using h

theorem scalar_bound_of_prefix_catalog_and_four (HC : ShortPrefixCatalogBounds)
    (H4 : FourPathCountBound) (F : Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ENNReal)*((7/10 : NNReal) : ENNReal) :=
  scalarSum_le_of_uniform_kp (uniformKP_of_prefix_catalog_and_four HC H4) F cut

theorem uniform_rooted_summability_of_prefix_catalog_and_four
    (HC : ShortPrefixCatalogBounds) (H4 : FourPathCountBound) : UniformRootedSummability :=
  uniform_rooted_summability_of_uniform_kp (uniformKP_of_prefix_catalog_and_four HC H4)

end
end RootedKP.AKLT
