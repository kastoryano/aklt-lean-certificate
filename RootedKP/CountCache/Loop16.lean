import RootedKP.CodeCountCertificates
import RootedKP.Arithmetic
namespace RootedKP.CachedPaths
open Arithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def certLoop16 : List ℕ × (ℕ × List ℕ) := ([84, 85, 87, 144, 146, 147],(0xd00000000000000b000000000000000000000,[0, 2, 0, 3, 0, 13, 0, 37, 1, 112, 21, 344]))
theorem checkedCertLoop16 : codeCertificateChecked L6Counts certLoop16 := by
  decide +kernel

def certLoop17 : List ℕ × (ℕ × List ℕ) := ([86, 87, 91, 146, 150, 151],(0xc400000000000008c000000000000000000000,[0, 0, 0, 0, 0, 6, 0, 20, 0, 74, 10, 259]))
theorem checkedCertLoop17 : codeCertificateChecked L6Counts certLoop17 := by
  decide +kernel

def certLoop18 : List ℕ × (ℕ × List ℕ) := ([90, 91, 95, 150, 154, 155],(0xc400000000000008c0000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 105]))
theorem checkedCertLoop18 : codeCertificateChecked L6Counts certLoop18 := by
  decide +kernel

def certLoop19 : List ℕ × (ℕ × List ℕ) := ([94, 95, 111, 154, 158, 159],(0xc400000000008000c00000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop19 : codeCertificateChecked L6Counts certLoop19 := by
  decide +kernel

def certLoop20 : List ℕ × (ℕ × List ℕ) := ([98, 100, 101, 162, 163, 165],(0x2c0000000000000034000000000000000000000000,[0, 2, 0, 3, 0, 13, 0, 37, 1, 112, 21, 344]))
theorem checkedCertLoop20 : codeCertificateChecked L6Counts certLoop20 := by
  decide +kernel

def certLoop21 : List ℕ × (ℕ × List ℕ) := ([98, 99, 102, 163, 166, 167],(0xc8000000000000004c000000000000000000000000,[0, 0, 0, 0, 0, 6, 0, 20, 0, 74, 10, 259]))
theorem checkedCertLoop21 : codeCertificateChecked L6Counts certLoop21 := by
  decide +kernel

def certLoop22 : List ℕ × (ℕ × List ℕ) := ([102, 103, 106, 167, 170, 171],(0xc8000000000000004c0000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 105]))
theorem checkedCertLoop22 : codeCertificateChecked L6Counts certLoop22 := by
  decide +kernel

def certLoop23 : List ℕ × (ℕ × List ℕ) := ([106, 107, 110, 171, 174, 175],(0xc8000000000000004c00000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop23 : codeCertificateChecked L6Counts certLoop23 := by
  decide +kernel

def certLoop24 : List ℕ × (ℕ × List ℕ) := ([110, 111, 158, 175, 178, 179],(0xc8000400000000000c000000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop24 : codeCertificateChecked L6Counts certLoop24 := by
  decide +kernel

def certLoop25 : List ℕ × (ℕ × List ℕ) := ([144, 145, 147, 220, 222, 223],(0xd000000000000000000b000000000000000000000000000000000000,[0, 2, 0, 3, 0, 13, 0, 37, 0, 113, 1, 359]))
theorem checkedCertLoop25 : codeCertificateChecked L6Counts certLoop25 := by
  decide +kernel

def certLoop26 : List ℕ × (ℕ × List ℕ) := ([146, 147, 151, 222, 226, 227],(0xc4000000000000000008c000000000000000000000000000000000000,[0, 0, 0, 0, 0, 6, 0, 20, 0, 74, 0, 267]))
theorem checkedCertLoop26 : codeCertificateChecked L6Counts certLoop26 := by
  decide +kernel

def certLoop27 : List ℕ × (ℕ × List ℕ) := ([150, 151, 155, 226, 230, 231],(0xc4000000000000000008c0000000000000000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 105]))
theorem checkedCertLoop27 : codeCertificateChecked L6Counts certLoop27 := by
  decide +kernel

def certLoop28 : List ℕ × (ℕ × List ℕ) := ([154, 155, 159, 230, 234, 235],(0xc4000000000000000008c00000000000000000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop28 : codeCertificateChecked L6Counts certLoop28 := by
  decide +kernel

def certLoop29 : List ℕ × (ℕ × List ℕ) := ([158, 159, 179, 234, 238, 239],(0xc4000000000000080000c000000000000000000000000000000000000000,[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))
theorem checkedCertLoop29 : codeCertificateChecked L6Counts certLoop29 := by
  decide +kernel

def certLoop30 : List ℕ × (ℕ × List ℕ) := ([162, 164, 165, 242, 243, 245],(0x2c000000000000000000340000000000000000000000000000000000000000,[0, 2, 0, 3, 0, 13, 0, 37, 0, 113, 1, 359]))
theorem checkedCertLoop30 : codeCertificateChecked L6Counts certLoop30 := by
  decide +kernel

def certLoop31 : List ℕ × (ℕ × List ℕ) := ([162, 163, 166, 243, 246, 247],(0xc80000000000000000004c0000000000000000000000000000000000000000,[0, 0, 0, 0, 0, 6, 0, 20, 0, 74, 0, 267]))
theorem checkedCertLoop31 : codeCertificateChecked L6Counts certLoop31 := by
  decide +kernel

end RootedKP.CachedPaths
