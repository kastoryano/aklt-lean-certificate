import RootedKP.PathCache.All
import RootedKP.CodeCache.StartU0
import RootedKP.CodeCache.StartU1
import RootedKP.CodeCache.StartU2
import RootedKP.CodeCache.StartU3
import RootedKP.CodeCache.StartU4
import RootedKP.CodeCache.StartU5
import RootedKP.CodeCache.StartU6
import RootedKP.CodeCache.StartU7
import RootedKP.CodeCache.StartU8
import RootedKP.CodeCache.StartU9
import RootedKP.CodeCache.StartU10
import RootedKP.CodeCache.StartU11
import RootedKP.CodeCache.StartU12
import RootedKP.CodeCache.StartU13
import RootedKP.CodeCache.StartU14
import RootedKP.CodeCache.StartU15
import RootedKP.CodeCache.StartU16
import RootedKP.CodeCache.StartU17
import RootedKP.CodeCache.StartU18
import RootedKP.CodeCache.StartU19
import RootedKP.CodeCache.StartU20
import RootedKP.CodeCache.StartU21
import RootedKP.CodeCache.StartU22
import RootedKP.CodeCache.StartU23
import RootedKP.CodeCache.StartU24
import RootedKP.CodeCache.StartU25
import RootedKP.CodeCache.StartU26
import RootedKP.CodeCache.StartU27
import RootedKP.CodeCache.StartU28
import RootedKP.CodeCache.StartU29
import RootedKP.CodeCache.StartU30
import RootedKP.CodeCache.StartU31
import RootedKP.CodeCache.StartL0
import RootedKP.CodeCache.StartL1
import RootedKP.CodeCache.StartL2
import RootedKP.CodeCache.StartL3
import RootedKP.CodeCache.StartL4
import RootedKP.CodeCache.StartL5
import RootedKP.CodeCache.StartL6
import RootedKP.CodeCache.StartL7
import RootedKP.CodeCache.StartL8
import RootedKP.CodeCache.StartL9
import RootedKP.CodeCache.StartL10
import RootedKP.CodeCache.StartL11
import RootedKP.CodeCache.StartL12
import RootedKP.CodeCache.StartL13
import RootedKP.CodeCache.StartL14
import RootedKP.CodeCache.StartL15
import RootedKP.CodeCache.StartL16
import RootedKP.CodeCache.StartL17
import RootedKP.CodeCache.StartL18
import RootedKP.CodeCache.StartL19
import RootedKP.CodeCache.StartL20
import RootedKP.CodeCache.StartL21
import RootedKP.CodeCache.StartL22
import RootedKP.CodeCache.StartL23
import RootedKP.CodeCache.StartL24
import RootedKP.CodeCache.StartL25
import RootedKP.CodeCache.StartL26
import RootedKP.CodeCache.StartL27
import RootedKP.CodeCache.StartL28
import RootedKP.CodeCache.StartL29
import RootedKP.CodeCache.StartL30
import RootedKP.CodeCache.StartL31

namespace RootedKP.CachedPaths
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def upperCodes (k n : ℕ) : List (List ℕ) := match k with
  | 0 => codeListsU0 n
  | 1 => codeListsU1 n
  | 2 => codeListsU2 n
  | 3 => codeListsU3 n
  | 4 => codeListsU4 n
  | 5 => codeListsU5 n
  | 6 => codeListsU6 n
  | 7 => codeListsU7 n
  | 8 => codeListsU8 n
  | 9 => codeListsU9 n
  | 10 => codeListsU10 n
  | 11 => codeListsU11 n
  | 12 => codeListsU12 n
  | 13 => codeListsU13 n
  | 14 => codeListsU14 n
  | 15 => codeListsU15 n
  | 16 => codeListsU16 n
  | 17 => codeListsU17 n
  | 18 => codeListsU18 n
  | 19 => codeListsU19 n
  | 20 => codeListsU20 n
  | 21 => codeListsU21 n
  | 22 => codeListsU22 n
  | 23 => codeListsU23 n
  | 24 => codeListsU24 n
  | 25 => codeListsU25 n
  | 26 => codeListsU26 n
  | 27 => codeListsU27 n
  | 28 => codeListsU28 n
  | 29 => codeListsU29 n
  | 30 => codeListsU30 n
  | 31 => codeListsU31 n
  | _ => []
theorem upper_code_cert (i : Fin 12) (k : Fin 32) :
    (upperCodes k.val (3+i.val)).map codeMask=upperMasks k.val (3+i.val) ∧
      ∀ys∈upperCodes k.val (3+i.val),ys.Pairwise (· ≤ ·) := by
  fin_cases k
  · exact certifiedCodesU0 i
  · exact certifiedCodesU1 i
  · exact certifiedCodesU2 i
  · exact certifiedCodesU3 i
  · exact certifiedCodesU4 i
  · exact certifiedCodesU5 i
  · exact certifiedCodesU6 i
  · exact certifiedCodesU7 i
  · exact certifiedCodesU8 i
  · exact certifiedCodesU9 i
  · exact certifiedCodesU10 i
  · exact certifiedCodesU11 i
  · exact certifiedCodesU12 i
  · exact certifiedCodesU13 i
  · exact certifiedCodesU14 i
  · exact certifiedCodesU15 i
  · exact certifiedCodesU16 i
  · exact certifiedCodesU17 i
  · exact certifiedCodesU18 i
  · exact certifiedCodesU19 i
  · exact certifiedCodesU20 i
  · exact certifiedCodesU21 i
  · exact certifiedCodesU22 i
  · exact certifiedCodesU23 i
  · exact certifiedCodesU24 i
  · exact certifiedCodesU25 i
  · exact certifiedCodesU26 i
  · exact certifiedCodesU27 i
  · exact certifiedCodesU28 i
  · exact certifiedCodesU29 i
  · exact certifiedCodesU30 i
  · exact certifiedCodesU31 i

def leftCodes (k n : ℕ) : List (List ℕ) := match k with
  | 0 => codeListsL0 n
  | 1 => codeListsL1 n
  | 2 => codeListsL2 n
  | 3 => codeListsL3 n
  | 4 => codeListsL4 n
  | 5 => codeListsL5 n
  | 6 => codeListsL6 n
  | 7 => codeListsL7 n
  | 8 => codeListsL8 n
  | 9 => codeListsL9 n
  | 10 => codeListsL10 n
  | 11 => codeListsL11 n
  | 12 => codeListsL12 n
  | 13 => codeListsL13 n
  | 14 => codeListsL14 n
  | 15 => codeListsL15 n
  | 16 => codeListsL16 n
  | 17 => codeListsL17 n
  | 18 => codeListsL18 n
  | 19 => codeListsL19 n
  | 20 => codeListsL20 n
  | 21 => codeListsL21 n
  | 22 => codeListsL22 n
  | 23 => codeListsL23 n
  | 24 => codeListsL24 n
  | 25 => codeListsL25 n
  | 26 => codeListsL26 n
  | 27 => codeListsL27 n
  | 28 => codeListsL28 n
  | 29 => codeListsL29 n
  | 30 => codeListsL30 n
  | 31 => codeListsL31 n
  | _ => []
theorem left_code_cert (i : Fin 12) (k : Fin 32) :
    (leftCodes k.val (3+i.val)).map codeMask=leftMasks k.val (3+i.val) ∧
      ∀ys∈leftCodes k.val (3+i.val),ys.Pairwise (· ≤ ·) := by
  fin_cases k
  · exact certifiedCodesL0 i
  · exact certifiedCodesL1 i
  · exact certifiedCodesL2 i
  · exact certifiedCodesL3 i
  · exact certifiedCodesL4 i
  · exact certifiedCodesL5 i
  · exact certifiedCodesL6 i
  · exact certifiedCodesL7 i
  · exact certifiedCodesL8 i
  · exact certifiedCodesL9 i
  · exact certifiedCodesL10 i
  · exact certifiedCodesL11 i
  · exact certifiedCodesL12 i
  · exact certifiedCodesL13 i
  · exact certifiedCodesL14 i
  · exact certifiedCodesL15 i
  · exact certifiedCodesL16 i
  · exact certifiedCodesL17 i
  · exact certifiedCodesL18 i
  · exact certifiedCodesL19 i
  · exact certifiedCodesL20 i
  · exact certifiedCodesL21 i
  · exact certifiedCodesL22 i
  · exact certifiedCodesL23 i
  · exact certifiedCodesL24 i
  · exact certifiedCodesL25 i
  · exact certifiedCodesL26 i
  · exact certifiedCodesL27 i
  · exact certifiedCodesL28 i
  · exact certifiedCodesL29 i
  · exact certifiedCodesL30 i
  · exact certifiedCodesL31 i

def codeCountByStarts (codes : List ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => codeCountByStarts codes n k+
      (codeHitCount codes (upperCodes k n)+codeHitCount codes (leftCodes k n))

theorem codeCountByStarts_eq (codes : List ℕ) (i : Fin 12) (k : ℕ) (hk : k ≤ 32) :
    codeCountByStarts codes (3+i.val) k=hitCount (codeMask codes) (cachedStarts (3+i.val) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hu := upper_code_cert i ⟨k,by omega⟩
    have hl := left_code_cert i ⟨k,by omega⟩
    simp only [codeCountByStarts,cachedStarts,hitCount_append,ih (by omega)]
    rw [codeHitCount_eq codes _ hu.2,hu.1,codeHitCount_eq codes _ hl.2,hl.1]

end RootedKP.CachedPaths
