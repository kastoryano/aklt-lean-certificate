import RootedKP.ShortRootCertificates.W3_17_U00
import RootedKP.ShortRootCertificates.W3_17_U01
import RootedKP.ShortRootCertificates.W3_17_U02
import RootedKP.ShortRootCertificates.W3_17_U03
import RootedKP.ShortRootCertificates.W3_17_U04
import RootedKP.ShortRootCertificates.W3_17_U05
import RootedKP.ShortRootCertificates.W3_17_U06
import RootedKP.ShortRootCertificates.W3_17_U07
import RootedKP.ShortRootCertificates.W3_17_U08
import RootedKP.ShortRootCertificates.W3_17_U09
import RootedKP.ShortRootCertificates.W3_17_L00
import RootedKP.ShortRootCertificates.W3_17_L01
import RootedKP.ShortRootCertificates.W3_17_L02
import RootedKP.ShortRootCertificates.W3_17_L03
import RootedKP.ShortRootCertificates.W3_17_L04
import RootedKP.ShortRootCertificates.W3_17_L05
import RootedKP.ShortRootCertificates.W3_17_L06
import RootedKP.ShortRootCertificates.W3_17_L07
import RootedKP.ShortRootCertificates.W3_17_L08
import RootedKP.ShortRootCertificates.W3_17_L09
namespace RootedKP.ShortRootCharts
theorem w3_count_17 : count cornerRootThree 17 = 868 := by
  rw [← prunedRootCount_eq,prunedRootCount_eq_sums]
  norm_num [Finset.sum_range_succ,w3_17_u_0, w3_17_u_1, w3_17_u_2, w3_17_u_3, w3_17_u_4, w3_17_u_5, w3_17_u_6, w3_17_u_7, w3_17_u_8, w3_17_u_9, w3_17_l_0, w3_17_l_1, w3_17_l_2, w3_17_l_3, w3_17_l_4, w3_17_l_5, w3_17_l_6, w3_17_l_7, w3_17_l_8, w3_17_l_9]
end RootedKP.ShortRootCharts
