import RootedKP.CountCache.Six0
import RootedKP.CountCache.Six16
import RootedKP.CountCache.Six32

namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certificatesSix : List (List ℕ × (ℕ × List ℕ)) := [certSix0,certSix1,certSix2,certSix3,certSix4,certSix5,certSix6,certSix7,certSix8,certSix9,certSix10,certSix11,certSix12,certSix13,certSix14,certSix15,certSix16,certSix17,certSix18,certSix19,certSix20,certSix21,certSix22,certSix23,certSix24,certSix25,certSix26,certSix27,certSix28,certSix29,certSix30,certSix31,certSix32,certSix33,certSix34]
def rowsSix : List (ℕ × List ℕ) := certificatesSix.map Prod.snd
theorem checkedCertificatesSix : ∀cert∈certificatesSix,codeCertificateChecked W6Counts cert := by
  simp only [certificatesSix,List.forall_mem_cons]
  exact ⟨checkedCertSix0,checkedCertSix1,checkedCertSix2,checkedCertSix3,checkedCertSix4,checkedCertSix5,checkedCertSix6,checkedCertSix7,checkedCertSix8,checkedCertSix9,checkedCertSix10,checkedCertSix11,checkedCertSix12,checkedCertSix13,checkedCertSix14,checkedCertSix15,checkedCertSix16,checkedCertSix17,checkedCertSix18,checkedCertSix19,checkedCertSix20,checkedCertSix21,checkedCertSix22,checkedCertSix23,checkedCertSix24,checkedCertSix25,checkedCertSix26,checkedCertSix27,checkedCertSix28,checkedCertSix29,checkedCertSix30,checkedCertSix31,checkedCertSix32,checkedCertSix33,checkedCertSix34,by simp⟩

theorem verifiedRowsSix : ∀row∈rowsSix,rowChecked allMasks W6Counts row := by
  intro row hr
  obtain ⟨cert,hc,rfl⟩ := List.mem_map.mp hr
  exact rowChecked_of_codeCertificate W6Counts cert (checkedCertificatesSix cert hc)

end RootedKP.CachedPaths
