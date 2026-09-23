import RootedKP.AKLTApplication
import RootedKP.FaceProbes

/-!
# Per-edge root counting from a six-edge KP probe

If every edge used by a polymer admits a six-edge polymer incompatible with
all polymers using that edge, the KP criterion itself bounds the per-edge
root mass by 7/10. `FaceProbes` supplies the literal geometric witnesses, so
the final theorems retain only the model-specific KP condition.
-/

namespace RootedKP.AKLT

open scoped BigOperators ENNReal NNReal Classical

/-- A six-edge polymer testing all polymers that use a given edge. -/
def SixEdgeProbeCover : Prop :=
  ∀ (F : Honeycomb.Rectangle) (e : Edge),
    (∃ p : Polymer F, e ∈ p.edges) →
    ∃ q : Polymer F, q.length = 6 ∧
      ∀ p : Polymer F, e ∈ p.edges → Polymer.Incompatible p q

/-- The actual honeycomb face geometry supplies every required probe. -/
theorem six_edge_probe_cover : SixEdgeProbeCover := face_probe_for_edge

/-- The budget agrees exactly with the summand in the literal KP criterion. -/
theorem rootBudget_eq_activity_exp {F : Honeycomb.Rectangle} (p : Polymer F) :
    rootBudget p = (p.activity : ℝ≥0∞) * ENNReal.ofReal (Real.exp p.cost) := by
  rw [rootBudget, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]

/-- Applying KP to the geometric probe controls all root polymers using the edge. -/
theorem edge_root_mass_le_of_kp_and_probes (hKP : UniformKPCondition)
    (hprobe : SixEdgeProbeCover) (F : Honeycomb.Rectangle) (e : Edge) :
    (∑' p : Polymer F, if e ∈ p.edges then rootBudget p else 0) ≤
      ((7 / 10 : ℝ≥0) : ℝ≥0∞) := by
  classical
  by_cases hused : ∃ p : Polymer F, e ∈ p.edges
  · obtain ⟨q, hlength, hq⟩ := hprobe F e hused
    have hcost : q.cost = (7 / 10 : ℝ) := by
      norm_num [Polymer.cost, hlength]
    calc
      (∑' p : Polymer F, if e ∈ p.edges then rootBudget p else 0) ≤
          ∑' p : Polymer F, if Polymer.Incompatible p q then
            (p.activity : ℝ≥0∞) * ENNReal.ofReal (Real.exp p.cost) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro p
        by_cases hp : e ∈ p.edges
        · simp only [if_pos hp, if_pos (hq p hp), rootBudget_eq_activity_exp]
          exact le_rfl
        · simp only [if_neg hp]
          exact zero_le
      _ ≤ ENNReal.ofReal q.cost := hKP F q
      _ = ((7 / 10 : ℝ≥0) : ℝ≥0∞) := by
        rw [hcost]
        change ENNReal.ofReal (((7 / 10 : ℝ≥0)) : ℝ) = _
        exact ENNReal.ofReal_coe_nnreal
  · have hempty : ∀ p : Polymer F, e ∉ p.edges := fun p hp => hused ⟨p, hp⟩
    simp only [if_neg (hempty _), tsum_zero]
    exact zero_le

/-- The formerly independent uniform root-mass hypothesis follows from KP and
six-edge probe geometry, with the explicit constant 7/10. -/
theorem uniform_root_mass_of_kp_and_probes (hKP : UniformKPCondition)
    (hprobe : SixEdgeProbeCover) : UniformRootMass :=
  ⟨7 / 10, edge_root_mass_le_of_kp_and_probes hKP hprobe⟩

/-- Explicit cut-size bound, retaining only KP and the stated geometric witness. -/
theorem scalarSum_le_of_kp_and_probes (hKP : UniformKPCondition)
    (hprobe : SixEdgeProbeCover) (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ℝ≥0∞) * ((7 / 10 : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [scalarSum_count_marks]
  calc
    (∑ e ∈ cut, ∑' p : Polymer F, if e ∈ p.edges then fixedRootMass F p else 0) ≤
        ∑ e ∈ cut, ((7 / 10 : ℝ≥0) : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro e _
      apply le_trans _ (edge_root_mass_le_of_kp_and_probes hKP hprobe F e)
      apply ENNReal.tsum_le_tsum
      intro p
      split_ifs
      · exact fixedRootMass_le_of_uniform_kp hKP F p
      · exact le_rfl
    _ = (cut.card : ℝ≥0∞) * ((7 / 10 : ℝ≥0) : ℝ≥0∞) := by simp [nsmul_eq_mul]

/-- Conditional uniform summability with no separate root-counting assumption. -/
theorem uniform_rooted_summability_of_kp_and_probes (hKP : UniformKPCondition)
    (hprobe : SixEdgeProbeCover) : UniformRootedSummability :=
  ⟨7 / 10, scalarSum_le_of_kp_and_probes hKP hprobe⟩

/-- Literal per-edge root counting follows from KP without an additional
root-counting hypothesis. -/
theorem edge_root_mass_le_of_uniform_kp (hKP : UniformKPCondition)
    (F : Honeycomb.Rectangle) (e : Edge) :
    (∑' p : Polymer F, if e ∈ p.edges then rootBudget p else 0) ≤
      ((7 / 10 : ℝ≥0) : ℝ≥0∞) :=
  edge_root_mass_le_of_kp_and_probes hKP six_edge_probe_cover F e

theorem uniform_root_mass_of_uniform_kp (hKP : UniformKPCondition) : UniformRootMass :=
  uniform_root_mass_of_kp_and_probes hKP six_edge_probe_cover

/-- The concrete scalar bound for every rectangle and cut, conditional only on
the model-specific KP criterion. -/
theorem scalarSum_le_of_uniform_kp (hKP : UniformKPCondition)
    (F : Honeycomb.Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ℝ≥0∞) * ((7 / 10 : ℝ≥0) : ℝ≥0∞) :=
  scalarSum_le_of_kp_and_probes hKP six_edge_probe_cover F cut

theorem uniform_rooted_summability_of_uniform_kp (hKP : UniformKPCondition) :
    UniformRootedSummability :=
  ⟨7 / 10, scalarSum_le_of_uniform_kp hKP⟩

end RootedKP.AKLT
