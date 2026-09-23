import RootedKP.CodeCountCertificates
import RootedKP.Arithmetic
namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certFour0 : List ℕ × (ℕ × List ℕ) := ([0, 1, 5, 8, 10],(0x523,[1, 2, 2, 2, 7, 9, 18, 21, 51, 61, 141, 180]))
theorem checkedCertFour0 : codeCertificateChecked W4Counts certFour0 := by
  decide +kernel

def certFour1 : List ℕ × (ℕ × List ℕ) := ([1, 8, 12, 13, 16],(0x13102,[0, 3, 1, 3, 4, 12, 14, 26, 46, 74, 140, 210]))
theorem checkedCertFour1 : codeCertificateChecked W4Counts certFour1 := by
  decide +kernel

def certFour2 : List ℕ × (ℕ × List ℕ) := ([4, 6, 7, 25, 27],(0xa0000d0,[1, 2, 2, 2, 7, 9, 18, 21, 51, 61, 141, 180]))
theorem checkedCertFour2 : codeCertificateChecked W4Counts certFour2 := by
  decide +kernel

def certFour3 : List ℕ × (ℕ × List ℕ) := ([6, 20, 21, 27, 31],(0x88300040,[0, 3, 1, 3, 4, 12, 14, 26, 46, 74, 140, 210]))
theorem checkedCertFour3 : codeCertificateChecked W4Counts certFour3 := by
  decide +kernel

def certFour4 : List ℕ × (ℕ × List ℕ) := ([13, 16, 40, 41, 44],(0x130000012000,[0, 3, 0, 4, 1, 14, 7, 34, 27, 92, 103, 262]))
theorem checkedCertFour4 : codeCertificateChecked W4Counts certFour4 := by
  decide +kernel

def certFour5 : List ℕ × (ℕ × List ℕ) := ([20, 31, 52, 53, 57],(0x230000080100000,[0, 3, 0, 4, 1, 14, 7, 34, 27, 92, 103, 262]))
theorem checkedCertFour5 : codeCertificateChecked W4Counts certFour5 := by
  decide +kernel

def certFour6 : List ℕ × (ℕ × List ℕ) := ([41, 44, 84, 85, 88],(0x13000000000120000000000,[0, 3, 0, 4, 0, 15, 1, 38, 11, 106, 51, 307]))
theorem checkedCertFour6 : codeCertificateChecked W4Counts certFour6 := by
  decide +kernel

def certFour7 : List ℕ × (ℕ × List ℕ) := ([52, 57, 100, 101, 105],(0x230000000000210000000000000,[0, 3, 0, 4, 0, 15, 1, 38, 11, 106, 51, 307]))
theorem checkedCertFour7 : codeCertificateChecked W4Counts certFour7 := by
  decide +kernel

def certFour8 : List ℕ × (ℕ × List ℕ) := ([85, 88, 144, 145, 148],(0x13000000000000012000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 1, 113, 16, 332]))
theorem checkedCertFour8 : codeCertificateChecked W4Counts certFour8 := by
  decide +kernel

def certFour9 : List ℕ × (ℕ × List ℕ) := ([100, 105, 164, 165, 169],(0x2300000000000000210000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 1, 113, 16, 332]))
theorem checkedCertFour9 : codeCertificateChecked W4Counts certFour9 := by
  decide +kernel

def certFour10 : List ℕ × (ℕ × List ℕ) := ([145, 148, 220, 221, 224],(0x130000000000000000012000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 1, 343]))
theorem checkedCertFour10 : codeCertificateChecked W4Counts certFour10 := by
  decide +kernel

def certFour11 : List ℕ × (ℕ × List ℕ) := ([164, 169, 244, 245, 249],(0x230000000000000000002100000000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 1, 343]))
theorem checkedCertFour11 : codeCertificateChecked W4Counts certFour11 := by
  decide +kernel

def certFour12 : List ℕ × (ℕ × List ℕ) := ([221, 224, 312, 313, 316],(0x13000000000000000000000120000000000000000000000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 0, 344]))
theorem checkedCertFour12 : codeCertificateChecked W4Counts certFour12 := by
  decide +kernel

def certFour13 : List ℕ × (ℕ × List ℕ) := ([244, 249, 340, 341, 345],(0x230000000000000000000000210000000000000000000000000000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 0, 344]))
theorem checkedCertFour13 : codeCertificateChecked W4Counts certFour13 := by
  decide +kernel

def certFour14 : List ℕ × (ℕ × List ℕ) := ([313, 316, 420, 421, 424],(0x13000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 0, 344]))
theorem checkedCertFour14 : codeCertificateChecked W4Counts certFour14 := by
  decide +kernel

def certFour15 : List ℕ × (ℕ × List ℕ) := ([340, 345, 452, 453, 457],(0x2300000000000000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000000000000,[0, 3, 0, 4, 0, 15, 0, 39, 0, 114, 0, 344]))
theorem checkedCertFour15 : codeCertificateChecked W4Counts certFour15 := by
  decide +kernel

end RootedKP.CachedPaths
