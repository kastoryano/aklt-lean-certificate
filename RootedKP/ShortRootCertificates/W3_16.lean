import RootedKP.ShortRootCertificates.W3_16_U00
import RootedKP.ShortRootCertificates.W3_16_U01
import RootedKP.ShortRootCertificates.W3_16_U02
import RootedKP.ShortRootCertificates.W3_16_U03
import RootedKP.ShortRootCertificates.W3_16_U04
import RootedKP.ShortRootCertificates.W3_16_U05
import RootedKP.ShortRootCertificates.W3_16_U06
import RootedKP.ShortRootCertificates.W3_16_U07
import RootedKP.ShortRootCertificates.W3_16_U08
import RootedKP.ShortRootCertificates.W3_16_L00
import RootedKP.ShortRootCertificates.W3_16_L01
import RootedKP.ShortRootCertificates.W3_16_L02
import RootedKP.ShortRootCertificates.W3_16_L03
import RootedKP.ShortRootCertificates.W3_16_L04
import RootedKP.ShortRootCertificates.W3_16_L05
import RootedKP.ShortRootCertificates.W3_16_L06
import RootedKP.ShortRootCertificates.W3_16_L07
import RootedKP.ShortRootCertificates.W3_16_L08
namespace RootedKP.ShortRootCharts
theorem w3_count_16 : count cornerRootThree 16 = 428 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_16_u_0, w3_16_u_1, w3_16_u_2, w3_16_u_3, w3_16_u_4, w3_16_u_5, w3_16_u_6, w3_16_u_7, w3_16_u_8, w3_16_l_0, w3_16_l_1, w3_16_l_2, w3_16_l_3, w3_16_l_4, w3_16_l_5, w3_16_l_6, w3_16_l_7, w3_16_l_8]
end RootedKP.ShortRootCharts
