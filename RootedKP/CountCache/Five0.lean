import RootedKP.CodeCountCertificates
import RootedKP.Arithmetic
namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certFive0 : List ℕ × (ℕ × List ℕ) := ([0, 1, 4, 5, 8, 25],(0x2000133,[1, 3, 2, 3, 7, 12, 19, 27, 55, 78, 156, 225]))
theorem checkedCertFive0 : codeCertificateChecked W5Counts certFive0 := by
  decide +kernel

def certFive1 : List ℕ × (ℕ × List ℕ) := ([4, 5, 6, 7, 10, 27],(0x80004f0,[1, 3, 2, 3, 7, 12, 19, 27, 55, 78, 156, 225]))
theorem checkedCertFive1 : codeCertificateChecked W5Counts certFive1 := by
  decide +kernel

end RootedKP.CachedPaths
