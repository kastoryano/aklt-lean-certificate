import RootedKP.CountCache.Five0

namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certificatesFive : List (List ℕ × (ℕ × List ℕ)) := [certFive0,certFive1]
def rowsFive : List (ℕ × List ℕ) := certificatesFive.map Prod.snd
theorem checkedCertificatesFive : ∀cert∈certificatesFive,codeCertificateChecked W5Counts cert := by
  simp only [certificatesFive,List.forall_mem_cons]
  exact ⟨checkedCertFive0,checkedCertFive1,by simp⟩

theorem verifiedRowsFive : ∀row∈rowsFive,rowChecked allMasks W5Counts row := by
  intro row hr
  obtain ⟨cert,hc,rfl⟩ := List.mem_map.mp hr
  exact rowChecked_of_codeCertificate W5Counts cert (checkedCertificatesFive cert hc)

end RootedKP.CachedPaths
