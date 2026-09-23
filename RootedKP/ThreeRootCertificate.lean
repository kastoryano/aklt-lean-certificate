import RootedKP.ShortRootCertificates.W3_03
import RootedKP.ShortRootCertificates.W3_04
import RootedKP.ShortRootCertificates.W3_05
import RootedKP.ShortRootCertificates.W3_06
import RootedKP.ShortRootCertificates.W3_07
import RootedKP.ShortRootCertificates.W3_08
import RootedKP.ShortRootCertificates.W3_09
import RootedKP.ShortRootCertificates.W3_10
import RootedKP.ShortRootCertificates.W3_11
import RootedKP.ShortRootCertificates.W3_12
import RootedKP.ShortRootCertificates.W3_13
import RootedKP.ShortRootCertificates.W3_14
import RootedKP.ShortRootCertificates.W3_15
import RootedKP.ShortRootCertificates.W3_16
import RootedKP.ShortRootCertificates.W3_17
import RootedKP.ShortRootCertificates.W3_18
import RootedKP.ShortRootCertificates.W3_19
import RootedKP.ShortRootCertificates.W3_20
import RootedKP.ThreeRootRegional
import RootedKP.CompletedLengthCounts
namespace RootedKP.ShortRootCharts

theorem w3_count_at (i : Fin 18) :
    count cornerRootThree (3+i.val) = Arithmetic.W3Counts[i.val]?.getD 0 := by
  fin_cases i <;> norm_num [Arithmetic.W3Counts,w3_count_03, w3_count_04, w3_count_05, w3_count_06, w3_count_07, w3_count_08, w3_count_09, w3_count_10, w3_count_11, w3_count_12, w3_count_13, w3_count_14, w3_count_15, w3_count_16, w3_count_17, w3_count_18, w3_count_19, w3_count_20]

end RootedKP.ShortRootCharts
namespace RootedKP.AKLT
open Arithmetic
open scoped Classical BigOperators
noncomputable section

theorem three_root_length_count {F : Honeycomb.Rectangle} (p : Polymer F)
    (hp : p.length=3) (i : ℕ) (hi : i<18) :
    pathLengthCount p i ≤ W3Counts[i]?.getD 0 := by
  have hh := three_root_family_count p hp (show 3+i≤20 by omega)
    ((shortPathSet p).filter (fun q => q.length=3+i)) (counted_path_spec p i)
  rw [ShortRootCharts.w3_count_at ⟨i,hi⟩] at hh
  exact hh

theorem three_root_cumulative {F : Honeycomb.Rectangle} (p : Polymer F)
    (hp : p.length=3) : CumulativePathBound p W3Counts := by
  refine ⟨rfl,?_⟩
  intro k hk
  unfold prefixSum
  apply Finset.sum_le_sum
  intro i hi
  exact_mod_cast three_root_length_count p hp i (by have := Finset.mem_range.mp hi; omega)

end
end RootedKP.AKLT
