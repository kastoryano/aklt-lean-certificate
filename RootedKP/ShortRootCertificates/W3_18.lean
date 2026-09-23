import RootedKP.ShortRootCertificates.W3_18_U00
import RootedKP.ShortRootCertificates.W3_18_U01
import RootedKP.ShortRootCertificates.W3_18_U02
import RootedKP.ShortRootCertificates.W3_18_U03
import RootedKP.ShortRootCertificates.W3_18_U04
import RootedKP.ShortRootCertificates.W3_18_U05
import RootedKP.ShortRootCertificates.W3_18_U06
import RootedKP.ShortRootCertificates.W3_18_U07
import RootedKP.ShortRootCertificates.W3_18_U08
import RootedKP.ShortRootCertificates.W3_18_U09
import RootedKP.ShortRootCertificates.W3_18_L00
import RootedKP.ShortRootCertificates.W3_18_L01
import RootedKP.ShortRootCertificates.W3_18_L02
import RootedKP.ShortRootCertificates.W3_18_L03
import RootedKP.ShortRootCertificates.W3_18_L04
import RootedKP.ShortRootCertificates.W3_18_L05
import RootedKP.ShortRootCertificates.W3_18_L06
import RootedKP.ShortRootCertificates.W3_18_L07
import RootedKP.ShortRootCertificates.W3_18_L08
import RootedKP.ShortRootCertificates.W3_18_L09
namespace RootedKP.ShortRootCharts
theorem w3_count_18 : count cornerRootThree 18 = 1284 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_18_u_0, w3_18_u_1, w3_18_u_2, w3_18_u_3, w3_18_u_4, w3_18_u_5, w3_18_u_6, w3_18_u_7, w3_18_u_8, w3_18_u_9, w3_18_l_0, w3_18_l_1, w3_18_l_2, w3_18_l_3, w3_18_l_4, w3_18_l_5, w3_18_l_6, w3_18_l_7, w3_18_l_8, w3_18_l_9]
end RootedKP.ShortRootCharts
