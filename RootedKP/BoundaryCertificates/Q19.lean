import RootedKP.BoundaryCertificates.Q19_00
import RootedKP.BoundaryCertificates.Q19_01
import RootedKP.BoundaryCertificates.Q19_02
import RootedKP.BoundaryCertificates.Q19_03
import RootedKP.BoundaryCertificates.Q19_04
import RootedKP.BoundaryCertificates.Q19_05
import RootedKP.BoundaryCertificates.Q19_06
import RootedKP.BoundaryCertificates.Q19_07
import RootedKP.BoundaryCertificates.Q19_08
import RootedKP.BoundaryCertificates.Q19_09
import RootedKP.BoundaryCertificates.Q19_10
import RootedKP.BoundaryCertificates.Q19_11
import RootedKP.BoundaryCertificates.Q19_12
import RootedKP.BoundaryCertificates.Q19_13
import RootedKP.BoundaryCertificates.Q19_14
import RootedKP.BoundaryCertificates.Q19_15
import RootedKP.BoundaryCertificates.Q19_16
import RootedKP.BoundaryCertificates.Q19_17
import RootedKP.BoundaryCertificates.Q19_18

namespace RootedKP.BoundaryCounts
open scoped BigOperators

theorem Q19 : cornerCount 19 = 6803 := by
  rw [cornerCount_eq_sum_starts]
  norm_num [Finset.sum_range_succ, Q19_start_0, Q19_start_1, Q19_start_2, Q19_start_3, Q19_start_4, Q19_start_5, Q19_start_6, Q19_start_7, Q19_start_8, Q19_start_9, Q19_start_10, Q19_start_11, Q19_start_12, Q19_start_13, Q19_start_14, Q19_start_15, Q19_start_16, Q19_start_17, Q19_start_18]

end RootedKP.BoundaryCounts
