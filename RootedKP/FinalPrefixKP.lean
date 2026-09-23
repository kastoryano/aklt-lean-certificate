import RootedKP.ShortPrefixCompletion
import RootedKP.FourPathCollar
namespace RootedKP.AKLT
open Honeycomb Arithmetic
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def relaxedCoefficient (n : ℕ) : ℚ := if n=4 then 4/5 else longCountCoefficient n
def relaxedFiniteAllowance (ell : ℚ) : ℚ :=
  ell*(∑i∈Finset.range 18,relaxedCoefficient (3+i)*weightCap (3+i))

theorem relaxed_length_bound {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    (i : ℕ) (hi : i < 18) :
    (pathLengthCount p i : ℝ)≤(p.length : ℝ)*(relaxedCoefficient (3+i) : ℝ) := by
  by_cases h4 : 3+i=4
  · have heq : i=1 := by omega
    subst i
    have hh : (5:ℝ)*(pathLengthCount p 1 : ℝ)≤4*(p.length : ℝ) := by
      exact_mod_cast four_root_count_relaxed p hp
    norm_num [relaxedCoefficient]
    linarith
  simp only [relaxedCoefficient,if_neg h4]
  by_cases h6 : 3+i=6
  · have heq : i=3 := by omega
    subst i
    exact long_six_length_bound p hp
  by_cases hodd : (3+i)%2=1
  · exact long_odd_length_bound p hp i hi hodd
  · exact long_even_length_bound p hp i hi (by omega) (by omega)

theorem relaxed_long_slope :
    pathFactor*((∑i∈Finset.range 18,relaxedCoefficient (3+i)*weightCap (3+i))+interiorTail)+
      loopMass≤slope := by
  norm_num [Finset.sum_range_succ,relaxedCoefficient,longCountCoefficient,weightCap,
    collarCoefficient,oddCounts,evenCountsFrom8,pathFactor,slope,rCap,qCap,
    interiorTail,tail0,tail1,loopMass,sumCounts,loopCounts]

theorem relaxed_long_envelope (F : Honeycomb.Rectangle) (p : Polymer F) (hp : 7 ≤ p.length) :
    shortPathEnvelope p ≤ (relaxedFiniteAllowance p.length : ℝ) := by
  classical
  have hlen : ∀ q ∈ shortPathSet p, 3 ≤ q.length ∧ q.length < 3 + 18 := by
    intro q hq
    have hh := (Finset.mem_filter.mp hq).2
    exact ⟨q.length_ge_three, by omega⟩
  calc
    shortPathEnvelope p = ∑ i ∈ Finset.range 18,
        (pathLengthCount p i : ℝ) * (weightCap (3 + i) : ℝ) :=
      weighted_sum_by_length (shortPathSet p) Polymer.length
        (fun n => (weightCap n : ℝ)) 3 18 hlen
    _ ≤ ∑ i ∈ Finset.range 18,
        ((p.length : ℝ) * (relaxedCoefficient (3 + i) : ℝ)) *
          (weightCap (3 + i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right (relaxed_length_bound p hp i (Finset.mem_range.mp hi))
      exact_mod_cast weightCap_nonneg (3 + i)
    _ = (p.length : ℝ) *
        ((∑ i ∈ Finset.range 18, relaxedCoefficient (3 + i) * weightCap (3 + i) : ℚ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (relaxedFiniteAllowance p.length : ℝ) := by
      simp [relaxedFiniteAllowance]

theorem long_kind_mass_bound {F : Rectangle} (p : Polymer F) (hp : 7≤p.length) :
    kindMass p .path+kindMass p .loop≤(a p.length : ℝ) := by
  have hs := relaxed_long_envelope F p hp
  have ht := regional_path_tail_bound F p
  have hpath := (kind_path_mass_le_envelopes p).trans
    (mul_le_mul_of_nonneg_left (add_le_add hs ht) (by norm_num : (0:ℝ)≤5/6))
  have hl : loopAllowance p≤(p.length : ℚ)*loopMass := by
    unfold loopAllowance
    split_ifs
    · nlinarith [loopMass_nonneg]
    · rfl
  have hlcast : (loopAllowance p : ℝ)≤(p.length : ℝ)*(loopMass : ℝ) := by exact_mod_cast hl
  have hloop := (loop_kindMass_le_allowance F p).trans hlcast
  let S : ℚ := ∑i∈Finset.range 18,relaxedCoefficient (3+i)*weightCap (3+i)
  have hcap : ((pathFactor*(S+interiorTail)+loopMass : ℚ) : ℝ)≤(slope : ℝ) := by
    exact_mod_cast relaxed_long_slope
  have hmul := mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg p.length : (0:ℝ)≤p.length)
  have hnot : ¬p.length≤6 := by omega
  have heq : (5/6:ℝ)*((relaxedFiniteAllowance p.length : ℝ)+(tailEnvelopeAllowance p : ℝ))+
      (p.length : ℝ)*(loopMass : ℝ)=
      (p.length : ℝ)*((pathFactor*(S+interiorTail)+loopMass : ℚ) : ℝ) := by
    simp only [relaxedFiniteAllowance,tailEnvelopeAllowance,if_neg hnot,pathFactor]
    dsimp only [S]
    push_cast
    ring
  have ha : a p.length=slope*(p.length : ℚ) := by
    unfold a
    split <;> first | omega | rfl
  calc
    _ ≤ (5/6:ℝ)*((relaxedFiniteAllowance p.length : ℝ)+(tailEnvelopeAllowance p : ℝ))+
        (p.length : ℝ)*(loopMass : ℝ) := add_le_add hpath hloop
    _ = _ := heq
    _ ≤ (p.length : ℝ)*(slope : ℝ) := hmul
    _ = _ := by rw [ha]; push_cast; ring

theorem uniformKP_of_prefix_catalog (HC : ShortPrefixCatalogBounds)
    : UniformKPCondition := by
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
    · exact long_kind_mass_bound p (by omega)
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => realBudget_nonneg q)] at h
  rw [tsum_fintype]
  simpa only [Finset.sum_filter,realBudget,ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal] using h

theorem scalar_bound_of_prefix_catalog (HC : ShortPrefixCatalogBounds)
    (F : Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ENNReal)*((7/10 : NNReal) : ENNReal) :=
  scalarSum_le_of_uniform_kp (uniformKP_of_prefix_catalog HC) F cut

theorem uniform_rooted_summability_of_prefix_catalog
    (HC : ShortPrefixCatalogBounds) : UniformRootedSummability :=
  uniform_rooted_summability_of_uniform_kp (uniformKP_of_prefix_catalog HC)

end
end RootedKP.AKLT
