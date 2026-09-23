import RootedKP.ShortRootCertificates.W3_20_U00
import RootedKP.ShortRootCertificates.W3_20_U01
import RootedKP.ShortRootCertificates.W3_20_U02
import RootedKP.ShortRootCertificates.W3_20_U03
import RootedKP.ShortRootCertificates.W3_20_U04
import RootedKP.ShortRootCertificates.W3_20_U05
import RootedKP.ShortRootCertificates.W3_20_U06
import RootedKP.ShortRootCertificates.W3_20_U07
import RootedKP.ShortRootCertificates.W3_20_U08
import RootedKP.ShortRootCertificates.W3_20_U09
import RootedKP.ShortRootCertificates.W3_20_U10
import RootedKP.ShortRootCertificates.W3_20_L00
import RootedKP.ShortRootCertificates.W3_20_L01
import RootedKP.ShortRootCertificates.W3_20_L02
import RootedKP.ShortRootCertificates.W3_20_L03
import RootedKP.ShortRootCertificates.W3_20_L04
import RootedKP.ShortRootCertificates.W3_20_L05
import RootedKP.ShortRootCertificates.W3_20_L06
import RootedKP.ShortRootCertificates.W3_20_L07
import RootedKP.ShortRootCertificates.W3_20_L08
import RootedKP.ShortRootCertificates.W3_20_L09
import RootedKP.ShortRootCertificates.W3_20_L10
namespace RootedKP.ShortRootCharts
theorem w3_count_20 : count cornerRootThree 20 = 3818 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_20_u_0, w3_20_u_1, w3_20_u_2, w3_20_u_3, w3_20_u_4, w3_20_u_5, w3_20_u_6, w3_20_u_7, w3_20_u_8, w3_20_u_9, w3_20_u_10, w3_20_l_0, w3_20_l_1, w3_20_l_2, w3_20_l_3, w3_20_l_4, w3_20_l_5, w3_20_l_6, w3_20_l_7, w3_20_l_8, w3_20_l_9, w3_20_l_10]
end RootedKP.ShortRootCharts
