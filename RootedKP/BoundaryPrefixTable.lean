import RootedKP.BoundaryCertificates.Side01
import RootedKP.BoundaryCertificates.Side02
import RootedKP.BoundaryCertificates.Side03
import RootedKP.BoundaryCertificates.Side04
import RootedKP.BoundaryCertificates.Side05
import RootedKP.BoundaryCertificates.Side06
import RootedKP.BoundaryCertificates.Side07
import RootedKP.BoundaryCertificates.Side08
import RootedKP.BoundaryCertificates.Side09
import RootedKP.BoundaryCertificates.Side10
import RootedKP.BoundaryCertificates.Corner01
import RootedKP.BoundaryCertificates.Corner02
import RootedKP.BoundaryCertificates.Corner03
import RootedKP.BoundaryCertificates.Corner04
import RootedKP.BoundaryCertificates.Corner05
import RootedKP.BoundaryCertificates.Corner06
import RootedKP.BoundaryCertificates.Corner07
import RootedKP.BoundaryCertificates.Corner08
import RootedKP.BoundaryCertificates.Corner09
import RootedKP.BoundaryCertificates.Corner10
import Mathlib.Tactic.FinCases

namespace RootedKP.BoundaryCounts

theorem side_prefix_checks : ∀ k : Fin 10, SidePrefixCheck (k.val + 1) := by
  intro k
  fin_cases k
  · exact side_prefix_1
  · exact side_prefix_2
  · exact side_prefix_3
  · exact side_prefix_4
  · exact side_prefix_5
  · exact side_prefix_6
  · exact side_prefix_7
  · exact side_prefix_8
  · exact side_prefix_9
  · exact side_prefix_10

theorem corner_prefix_checks : ∀ k : Fin 10, CornerPrefixCheck (k.val + 1) := by
  intro k
  fin_cases k
  · exact corner_prefix_1
  · exact corner_prefix_2
  · exact corner_prefix_3
  · exact corner_prefix_4
  · exact corner_prefix_5
  · exact corner_prefix_6
  · exact corner_prefix_7
  · exact corner_prefix_8
  · exact corner_prefix_9
  · exact corner_prefix_10

end RootedKP.BoundaryCounts
