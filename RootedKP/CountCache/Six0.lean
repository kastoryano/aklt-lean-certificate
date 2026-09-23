import RootedKP.CodeCountCertificates
import RootedKP.Arithmetic
namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certSix0 : List ℕ × (ℕ × List ℕ) := ([0, 1, 5, 10, 12, 13, 16],(0x13423,[1, 3, 2, 3, 7, 13, 20, 30, 62, 87, 183, 255]))
theorem checkedCertSix0 : codeCertificateChecked W6Counts certSix0 := by
  decide +kernel

def certSix1 : List ℕ × (ℕ × List ℕ) := ([4, 6, 7, 20, 21, 25, 31],(0x823000d0,[1, 3, 2, 3, 7, 13, 20, 30, 62, 87, 183, 255]))
theorem checkedCertSix1 : codeCertificateChecked W6Counts certSix1 := by
  decide +kernel

def certSix2 : List ℕ × (ℕ × List ℕ) := ([1, 8, 12, 13, 40, 41, 44],(0x130000003102,[0, 4, 1, 4, 4, 16, 14, 36, 49, 104, 161, 299]))
theorem checkedCertSix2 : codeCertificateChecked W6Counts certSix2 := by
  decide +kernel

def certSix3 : List ℕ × (ℕ × List ℕ) := ([6, 20, 21, 27, 52, 53, 57],(0x230000008300040,[0, 4, 1, 4, 4, 16, 14, 36, 49, 104, 161, 299]))
theorem checkedCertSix3 : codeCertificateChecked W6Counts certSix3 := by
  decide +kernel

def certSix4 : List ℕ × (ℕ × List ℕ) := ([13, 16, 40, 41, 84, 85, 88],(0x13000000000030000012000,[0, 4, 0, 5, 1, 18, 7, 44, 27, 124, 107, 360]))
theorem checkedCertSix4 : codeCertificateChecked W6Counts certSix4 := by
  decide +kernel

def certSix5 : List ℕ × (ℕ × List ℕ) := ([20, 31, 52, 53, 100, 101, 105],(0x230000000000030000080100000,[0, 4, 0, 5, 1, 18, 7, 44, 27, 124, 107, 360]))
theorem checkedCertSix5 : codeCertificateChecked W6Counts certSix5 := by
  decide +kernel

def certSix6 : List ℕ × (ℕ × List ℕ) := ([41, 44, 84, 85, 144, 145, 148],(0x13000000000000003000000000120000000000,[0, 4, 0, 5, 0, 19, 1, 48, 11, 138, 51, 408]))
theorem checkedCertSix6 : codeCertificateChecked W6Counts certSix6 := by
  decide +kernel

def certSix7 : List ℕ × (ℕ × List ℕ) := ([52, 57, 100, 101, 164, 165, 169],(0x2300000000000000030000000000210000000000000,[0, 4, 0, 5, 0, 19, 1, 48, 11, 138, 51, 408]))
theorem checkedCertSix7 : codeCertificateChecked W6Counts certSix7 := by
  decide +kernel

def certSix8 : List ℕ × (ℕ × List ℕ) := ([85, 88, 144, 145, 220, 221, 224],(0x130000000000000000003000000000000012000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 1, 145, 16, 433]))
theorem checkedCertSix8 : codeCertificateChecked W6Counts certSix8 := by
  decide +kernel

def certSix9 : List ℕ × (ℕ × List ℕ) := ([100, 105, 164, 165, 244, 245, 249],(0x230000000000000000000300000000000000210000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 1, 145, 16, 433]))
theorem checkedCertSix9 : codeCertificateChecked W6Counts certSix9 := by
  decide +kernel

def certSix10 : List ℕ × (ℕ × List ℕ) := ([145, 148, 220, 221, 312, 313, 316],(0x13000000000000000000000030000000000000000012000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 1, 444]))
theorem checkedCertSix10 : codeCertificateChecked W6Counts certSix10 := by
  decide +kernel

def certSix11 : List ℕ × (ℕ × List ℕ) := ([164, 169, 244, 245, 340, 341, 345],(0x230000000000000000000000030000000000000000002100000000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 1, 444]))
theorem checkedCertSix11 : codeCertificateChecked W6Counts certSix11 := by
  decide +kernel

def certSix12 : List ℕ × (ℕ × List ℕ) := ([221, 224, 312, 313, 420, 421, 424],(0x13000000000000000000000000003000000000000000000000120000000000000000000000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 0, 445]))
theorem checkedCertSix12 : codeCertificateChecked W6Counts certSix12 := by
  decide +kernel

def certSix13 : List ℕ × (ℕ × List ℕ) := ([244, 249, 340, 341, 452, 453, 457],(0x2300000000000000000000000000030000000000000000000000210000000000000000000000000000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 0, 445]))
theorem checkedCertSix13 : codeCertificateChecked W6Counts certSix13 := by
  decide +kernel

def certSix14 : List ℕ × (ℕ × List ℕ) := ([313, 316, 420, 421, 544, 545, 548],(0x130000000000000000000000000000003000000000000000000000000012000000000000000000000000000000000000000000000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 0, 445]))
theorem checkedCertSix14 : codeCertificateChecked W6Counts certSix14 := by
  decide +kernel

def certSix15 : List ℕ × (ℕ × List ℕ) := ([340, 345, 452, 453, 580, 581, 585],(0x230000000000000000000000000000000300000000000000000000000000210000000000000000000000000000000000000000000000000000000000000000000000000000000000000,[0, 4, 0, 5, 0, 19, 0, 49, 0, 146, 0, 445]))
theorem checkedCertSix15 : codeCertificateChecked W6Counts certSix15 := by
  decide +kernel

end RootedKP.CachedPaths
