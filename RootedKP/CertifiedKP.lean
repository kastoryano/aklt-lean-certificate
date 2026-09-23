import RootedKP.CertifiedShortPrefix
import RootedKP.FinalPrefixKP

/-! Final model-specific rooted KP and root-counting theorems. All geometric,
enumerative, arithmetic, and summability inputs are proved in this project. -/
namespace RootedKP.AKLT
open Honeycomb
open scoped Classical

theorem uniformKP_certified : UniformKPCondition :=
  uniformKP_of_prefix_catalog shortPrefixCatalogBounds

theorem edge_root_mass_certified (F : Rectangle) (e : Edge) :
    (∑' p : Polymer F, if e∈p.edges then rootBudget p else 0)≤
      ((7/10 : NNReal) : ENNReal) :=
  edge_root_mass_le_of_uniform_kp uniformKP_certified F e

theorem uniform_root_mass_certified : UniformRootMass :=
  uniform_root_mass_of_uniform_kp uniformKP_certified

theorem scalar_bound_certified (F : Rectangle) (cut : Finset Edge) :
    scalarSum F cut ≤ (cut.card : ENNReal)*((7/10 : NNReal) : ENNReal) :=
  scalar_bound_of_prefix_catalog shortPrefixCatalogBounds F cut

theorem rooted_summability_certified : UniformRootedSummability :=
  uniform_rooted_summability_of_prefix_catalog shortPrefixCatalogBounds

end RootedKP.AKLT
