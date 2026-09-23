import RootedKP.ThreeRootCertificate
import RootedKP.ShortCatalogBounds
import RootedKP.SixPathCounts
import RootedKP.PathTailCounting
import RootedKP.KPCompletion

/-! Exact remaining obligations. Neither is asserted here: this module proves
that these two explicit inputs suffice for the complete AKLT rooted bound. -/
namespace RootedKP.AKLT
open Honeycomb Arithmetic ShortRootRepresentatives
noncomputable section

/-- The only outstanding long-root count. The stronger paper estimate
`2 * count ≤ length + 2` implies this bound for roots of length at least seven. -/
def FourPathCountBound : Prop := ∀(F : Rectangle)(p : Polymer F),
  7≤p.length → 14*pathLengthCount p 1≤9*p.length

theorem long_length_count_bound_of_four (H : FourPathCountBound) :
    LongLengthCountBound := by
  intro F p hp i hi
  by_cases h4 : 3+i=4
  · have heq : i=1 := by omega
    subst i
    have hh : (14:ℝ)*(pathLengthCount p 1 : ℝ)≤9*(p.length : ℝ) := by
      exact_mod_cast H F p hp
    norm_num [longCountCoefficient]
    linarith
  by_cases h6 : 3+i=6
  · have heq : i=3 := by omega
    subst i
    exact long_six_length_bound p hp
  by_cases hodd : (3+i)%2=1
  · exact long_odd_length_bound p hp i hi hodd
  · exact long_even_length_bound p hp i hi (by omega) (by omega)

theorem unweighted_counts_of_catalog_and_four (HC : ShortCatalogBounds)
    (H4 : FourPathCountBound) : UnweightedPathCountingInputs where
  shortRoots := by
    intro F p hp
    cases hk : p.kind with
    | path =>
      simp only [hk,ite_true]
      by_cases h3 : p.length=3
      · simpa only [h3,shortCounts] using three_root_cumulative p h3
      · have hmin := p.length_ge_three
        exact short_path_cumulative_of_catalog HC p hk (by omega) hp
    | loop =>
      simp only [hk,show Kind.loop≠Kind.path by decide,ite_false]
      exact short_loop_cumulative_of_catalog HC p hk hp
  longRoots := long_length_count_bound_of_four H4
  tails := tail_length_count_bound

theorem uniformKP_of_catalog_and_four (HC : ShortCatalogBounds) (H4 : FourPathCountBound) :
    UniformKPCondition :=
  uniformKP_of_unweighted_path_counts (unweighted_counts_of_catalog_and_four HC H4)

theorem scalar_bound_of_catalog_and_four (HC : ShortCatalogBounds) (H4 : FourPathCountBound)
    (F : Rectangle) (cut : Finset Edge) :
    scalarSum F cut≤(cut.card : ENNReal)*((7/10 : NNReal) : ENNReal) :=
  scalar_bound_of_unweighted_path_counts (unweighted_counts_of_catalog_and_four HC H4) F cut

theorem uniform_rooted_summability_of_catalog_and_four
    (HC : ShortCatalogBounds) (H4 : FourPathCountBound) : UniformRootedSummability :=
  uniform_rooted_summability_of_unweighted_path_counts
    (unweighted_counts_of_catalog_and_four HC H4)

end
end RootedKP.AKLT
