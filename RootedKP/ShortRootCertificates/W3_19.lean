import RootedKP.ShortRootCertificates.W3_19_U00
import RootedKP.ShortRootCertificates.W3_19_U01
import RootedKP.ShortRootCertificates.W3_19_U02
import RootedKP.ShortRootCertificates.W3_19_U03
import RootedKP.ShortRootCertificates.W3_19_U04
import RootedKP.ShortRootCertificates.W3_19_U05
import RootedKP.ShortRootCertificates.W3_19_U06
import RootedKP.ShortRootCertificates.W3_19_U07
import RootedKP.ShortRootCertificates.W3_19_U08
import RootedKP.ShortRootCertificates.W3_19_U09
import RootedKP.ShortRootCertificates.W3_19_U10
import RootedKP.ShortRootCertificates.W3_19_L00
import RootedKP.ShortRootCertificates.W3_19_L01
import RootedKP.ShortRootCertificates.W3_19_L02
import RootedKP.ShortRootCertificates.W3_19_L03
import RootedKP.ShortRootCertificates.W3_19_L04
import RootedKP.ShortRootCertificates.W3_19_L05
import RootedKP.ShortRootCertificates.W3_19_L06
import RootedKP.ShortRootCertificates.W3_19_L07
import RootedKP.ShortRootCertificates.W3_19_L08
import RootedKP.ShortRootCertificates.W3_19_L09
import RootedKP.ShortRootCertificates.W3_19_L10
namespace RootedKP.ShortRootCharts
theorem w3_count_19 : count cornerRootThree 19 = 2530 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_19_u_0, w3_19_u_1, w3_19_u_2, w3_19_u_3, w3_19_u_4, w3_19_u_5, w3_19_u_6, w3_19_u_7, w3_19_u_8, w3_19_u_9, w3_19_u_10, w3_19_l_0, w3_19_l_1, w3_19_l_2, w3_19_l_3, w3_19_l_4, w3_19_l_5, w3_19_l_6, w3_19_l_7, w3_19_l_8, w3_19_l_9, w3_19_l_10]
end RootedKP.ShortRootCharts
