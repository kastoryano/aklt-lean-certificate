import RootedKP.CountCache.Four0
import RootedKP.CountCache.Four16
import RootedKP.CountCache.Four32

namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certificatesFour : List (List ℕ × (ℕ × List ℕ)) := [certFour0,certFour1,certFour2,certFour3,certFour4,certFour5,certFour6,certFour7,certFour8,certFour9,certFour10,certFour11,certFour12,certFour13,certFour14,certFour15,certFour16,certFour17,certFour18,certFour19,certFour20,certFour21,certFour22,certFour23,certFour24,certFour25,certFour26,certFour27,certFour28,certFour29,certFour30,certFour31,certFour32,certFour33,certFour34]
def rowsFour : List (ℕ × List ℕ) := certificatesFour.map Prod.snd
theorem checkedCertificatesFour : ∀cert∈certificatesFour,codeCertificateChecked W4Counts cert := by
  simp only [certificatesFour,List.forall_mem_cons]
  exact ⟨checkedCertFour0,checkedCertFour1,checkedCertFour2,checkedCertFour3,checkedCertFour4,checkedCertFour5,checkedCertFour6,checkedCertFour7,checkedCertFour8,checkedCertFour9,checkedCertFour10,checkedCertFour11,checkedCertFour12,checkedCertFour13,checkedCertFour14,checkedCertFour15,checkedCertFour16,checkedCertFour17,checkedCertFour18,checkedCertFour19,checkedCertFour20,checkedCertFour21,checkedCertFour22,checkedCertFour23,checkedCertFour24,checkedCertFour25,checkedCertFour26,checkedCertFour27,checkedCertFour28,checkedCertFour29,checkedCertFour30,checkedCertFour31,checkedCertFour32,checkedCertFour33,checkedCertFour34,by simp⟩

theorem verifiedRowsFour : ∀row∈rowsFour,rowChecked allMasks W4Counts row := by
  intro row hr
  obtain ⟨cert,hc,rfl⟩ := List.mem_map.mp hr
  exact rowChecked_of_codeCertificate W4Counts cert (checkedCertificatesFour cert hc)

end RootedKP.CachedPaths
