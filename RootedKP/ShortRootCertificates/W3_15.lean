import RootedKP.ShortRootCertificates.W3_15_U00
import RootedKP.ShortRootCertificates.W3_15_U01
import RootedKP.ShortRootCertificates.W3_15_U02
import RootedKP.ShortRootCertificates.W3_15_U03
import RootedKP.ShortRootCertificates.W3_15_U04
import RootedKP.ShortRootCertificates.W3_15_U05
import RootedKP.ShortRootCertificates.W3_15_U06
import RootedKP.ShortRootCertificates.W3_15_U07
import RootedKP.ShortRootCertificates.W3_15_U08
import RootedKP.ShortRootCertificates.W3_15_L00
import RootedKP.ShortRootCertificates.W3_15_L01
import RootedKP.ShortRootCertificates.W3_15_L02
import RootedKP.ShortRootCertificates.W3_15_L03
import RootedKP.ShortRootCertificates.W3_15_L04
import RootedKP.ShortRootCertificates.W3_15_L05
import RootedKP.ShortRootCertificates.W3_15_L06
import RootedKP.ShortRootCertificates.W3_15_L07
import RootedKP.ShortRootCertificates.W3_15_L08
namespace RootedKP.ShortRootCharts
theorem w3_count_15 : count cornerRootThree 15 = 296 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_15_u_0, w3_15_u_1, w3_15_u_2, w3_15_u_3, w3_15_u_4, w3_15_u_5, w3_15_u_6, w3_15_u_7, w3_15_u_8, w3_15_l_0, w3_15_l_1, w3_15_l_2, w3_15_l_3, w3_15_l_4, w3_15_l_5, w3_15_l_6, w3_15_l_7, w3_15_l_8]
end RootedKP.ShortRootCharts
