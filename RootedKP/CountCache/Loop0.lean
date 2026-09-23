import RootedKP.CodeCountCertificates
import RootedKP.Arithmetic
namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certLoop0 : List ℕ × (ℕ × List ℕ) := ([0, 2, 3, 4, 5, 7],(0xbd,[1, 2, 2, 2, 7, 10, 20, 24, 60, 70, 174, 210]))
theorem checkedCertLoop0 : codeCertificateChecked L6Counts certLoop0 := by
  decide +kernel

def certLoop1 : List ℕ × (ℕ × List ℕ) := ([0, 1, 3, 12, 14, 15],(0xd00b,[0, 2, 1, 2, 6, 10, 17, 24, 58, 73, 179, 221]))
theorem checkedCertLoop1 : codeCertificateChecked L6Counts certLoop1 := by
  decide +kernel

def certLoop2 : List ℕ × (ℕ × List ℕ) := ([2, 6, 7, 18, 19, 21],(0x2c00c4,[0, 2, 1, 2, 6, 10, 17, 24, 58, 73, 179, 221]))
theorem checkedCertLoop2 : codeCertificateChecked L6Counts certLoop2 := by
  decide +kernel

def certLoop3 : List ℕ × (ℕ × List ℕ) := ([2, 3, 14, 19, 22, 23],(0xc8400c,[0, 0, 0, 0, 4, 8, 16, 18, 55, 64, 182, 206]))
theorem checkedCertLoop3 : codeCertificateChecked L6Counts certLoop3 := by
  decide +kernel

def certLoop4 : List ℕ × (ℕ × List ℕ) := ([12, 13, 15, 40, 42, 43],(0xd000000b000,[0, 2, 0, 3, 1, 12, 10, 30, 37, 86, 137, 256]))
theorem checkedCertLoop4 : codeCertificateChecked L6Counts certLoop4 := by
  decide +kernel

def certLoop5 : List ℕ × (ℕ × List ℕ) := ([14, 15, 23, 42, 46, 47],(0xc4000080c000,[0, 0, 0, 0, 0, 6, 6, 16, 37, 60, 139, 198]))
theorem checkedCertLoop5 : codeCertificateChecked L6Counts certLoop5 := by
  decide +kernel

def certLoop6 : List ℕ × (ℕ × List ℕ) := ([18, 20, 21, 50, 51, 53],(0x2c000000340000,[0, 2, 0, 3, 1, 12, 10, 30, 37, 86, 137, 256]))
theorem checkedCertLoop6 : codeCertificateChecked L6Counts certLoop6 := by
  decide +kernel

def certLoop7 : List ℕ × (ℕ × List ℕ) := ([18, 19, 22, 51, 54, 55],(0xc80000004c0000,[0, 0, 0, 0, 0, 6, 6, 16, 37, 60, 139, 198]))
theorem checkedCertLoop7 : codeCertificateChecked L6Counts certLoop7 := by
  decide +kernel

def certLoop8 : List ℕ × (ℕ × List ℕ) := ([22, 23, 46, 55, 58, 59],(0xc80400000c00000,[0, 0, 0, 0, 0, 0, 0, 0, 16, 32, 100, 124]))
theorem checkedCertLoop8 : codeCertificateChecked L6Counts certLoop8 := by
  decide +kernel

def certLoop9 : List ℕ × (ℕ × List ℕ) := ([40, 41, 43, 84, 86, 87],(0xd0000000000b0000000000,[0, 2, 0, 3, 0, 13, 1, 36, 15, 102, 72, 311]))
theorem checkedCertLoop9 : codeCertificateChecked L6Counts certLoop9 := by
  decide +kernel

def certLoop10 : List ℕ × (ℕ × List ℕ) := ([42, 43, 47, 86, 90, 91],(0xc40000000008c0000000000,[0, 0, 0, 0, 0, 6, 0, 20, 8, 68, 67, 228]))
theorem checkedCertLoop10 : codeCertificateChecked L6Counts certLoop10 := by
  decide +kernel

def certLoop11 : List ℕ × (ℕ × List ℕ) := ([46, 47, 59, 90, 94, 95],(0xc40000000800c00000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 28, 93]))
theorem checkedCertLoop11 : codeCertificateChecked L6Counts certLoop11 := by
  decide +kernel

def certLoop12 : List ℕ × (ℕ × List ℕ) := ([50, 52, 53, 98, 99, 101],(0x2c000000000034000000000000,[0, 2, 0, 3, 0, 13, 1, 36, 15, 102, 72, 311]))
theorem checkedCertLoop12 : codeCertificateChecked L6Counts certLoop12 := by
  decide +kernel

def certLoop13 : List ℕ × (ℕ × List ℕ) := ([50, 51, 54, 99, 102, 103],(0xc800000000004c000000000000,[0, 0, 0, 0, 0, 6, 0, 20, 8, 68, 67, 228]))
theorem checkedCertLoop13 : codeCertificateChecked L6Counts certLoop13 := by
  decide +kernel

def certLoop14 : List ℕ × (ℕ × List ℕ) := ([54, 55, 58, 103, 106, 107],(0xc800000000004c0000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 28, 93]))
theorem checkedCertLoop14 : codeCertificateChecked L6Counts certLoop14 := by
  decide +kernel

def certLoop15 : List ℕ × (ℕ × List ℕ) := ([58, 59, 94, 107, 110, 111],(0xc800400000000c00000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop15 : codeCertificateChecked L6Counts certLoop15 := by
  decide +kernel

end RootedKP.CachedPaths
