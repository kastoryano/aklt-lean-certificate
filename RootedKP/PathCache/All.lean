import RootedKP.CachedPathAssembly
import RootedKP.PathCache.StartU0
import RootedKP.PathCache.StartU1
import RootedKP.PathCache.StartU2
import RootedKP.PathCache.StartU3
import RootedKP.PathCache.StartU4
import RootedKP.PathCache.StartU5
import RootedKP.PathCache.StartU6
import RootedKP.PathCache.StartU7
import RootedKP.PathCache.StartU8
import RootedKP.PathCache.StartU9
import RootedKP.PathCache.StartU10
import RootedKP.PathCache.StartU11
import RootedKP.PathCache.StartU12
import RootedKP.PathCache.StartU13
import RootedKP.PathCache.StartU14
import RootedKP.PathCache.StartU15
import RootedKP.PathCache.StartU16
import RootedKP.PathCache.StartU17
import RootedKP.PathCache.StartU18
import RootedKP.PathCache.StartU19
import RootedKP.PathCache.StartU20
import RootedKP.PathCache.StartU21
import RootedKP.PathCache.StartU22
import RootedKP.PathCache.StartU23
import RootedKP.PathCache.StartU24
import RootedKP.PathCache.StartU25
import RootedKP.PathCache.StartU26
import RootedKP.PathCache.StartU27
import RootedKP.PathCache.StartU28
import RootedKP.PathCache.StartU29
import RootedKP.PathCache.StartU30
import RootedKP.PathCache.StartU31
import RootedKP.PathCache.StartL0
import RootedKP.PathCache.StartL1
import RootedKP.PathCache.StartL2
import RootedKP.PathCache.StartL3
import RootedKP.PathCache.StartL4
import RootedKP.PathCache.StartL5
import RootedKP.PathCache.StartL6
import RootedKP.PathCache.StartL7
import RootedKP.PathCache.StartL8
import RootedKP.PathCache.StartL9
import RootedKP.PathCache.StartL10
import RootedKP.PathCache.StartL11
import RootedKP.PathCache.StartL12
import RootedKP.PathCache.StartL13
import RootedKP.PathCache.StartL14
import RootedKP.PathCache.StartL15
import RootedKP.PathCache.StartL16
import RootedKP.PathCache.StartL17
import RootedKP.PathCache.StartL18
import RootedKP.PathCache.StartL19
import RootedKP.PathCache.StartL20
import RootedKP.PathCache.StartL21
import RootedKP.PathCache.StartL22
import RootedKP.PathCache.StartL23
import RootedKP.PathCache.StartL24
import RootedKP.PathCache.StartL25
import RootedKP.PathCache.StartL26
import RootedKP.PathCache.StartL27
import RootedKP.PathCache.StartL28
import RootedKP.PathCache.StartL29
import RootedKP.PathCache.StartL30
import RootedKP.PathCache.StartL31

namespace RootedKP.CachedPaths
open Honeycomb PackedSupports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def upperMasks (k n : ℕ) : List ℕ := match k with
  | 0 => masksU0 n
  | 1 => masksU1 n
  | 2 => masksU2 n
  | 3 => masksU3 n
  | 4 => masksU4 n
  | 5 => masksU5 n
  | 6 => masksU6 n
  | 7 => masksU7 n
  | 8 => masksU8 n
  | 9 => masksU9 n
  | 10 => masksU10 n
  | 11 => masksU11 n
  | 12 => masksU12 n
  | 13 => masksU13 n
  | 14 => masksU14 n
  | 15 => masksU15 n
  | 16 => masksU16 n
  | 17 => masksU17 n
  | 18 => masksU18 n
  | 19 => masksU19 n
  | 20 => masksU20 n
  | 21 => masksU21 n
  | 22 => masksU22 n
  | 23 => masksU23 n
  | 24 => masksU24 n
  | 25 => masksU25 n
  | 26 => masksU26 n
  | 27 => masksU27 n
  | 28 => masksU28 n
  | 29 => masksU29 n
  | 30 => masksU30 n
  | 31 => masksU31 n
  | _ => []

theorem upper_checked (i : Fin 12) (k : Fin 32) :
    gather (upperStart k.val) (3+i.val) [upperStart k.val]=
      upperMasks k.val (3+i.val) := by
  fin_cases k
  · exact checkedU0 i
  · exact checkedU1 i
  · exact checkedU2 i
  · exact checkedU3 i
  · exact checkedU4 i
  · exact checkedU5 i
  · exact checkedU6 i
  · exact checkedU7 i
  · exact checkedU8 i
  · exact checkedU9 i
  · exact checkedU10 i
  · exact checkedU11 i
  · exact checkedU12 i
  · exact checkedU13 i
  · exact checkedU14 i
  · exact checkedU15 i
  · exact checkedU16 i
  · exact checkedU17 i
  · exact checkedU18 i
  · exact checkedU19 i
  · exact checkedU20 i
  · exact checkedU21 i
  · exact checkedU22 i
  · exact checkedU23 i
  · exact checkedU24 i
  · exact checkedU25 i
  · exact checkedU26 i
  · exact checkedU27 i
  · exact checkedU28 i
  · exact checkedU29 i
  · exact checkedU30 i
  · exact checkedU31 i

def leftMasks (k n : ℕ) : List ℕ := match k with
  | 0 => masksL0 n
  | 1 => masksL1 n
  | 2 => masksL2 n
  | 3 => masksL3 n
  | 4 => masksL4 n
  | 5 => masksL5 n
  | 6 => masksL6 n
  | 7 => masksL7 n
  | 8 => masksL8 n
  | 9 => masksL9 n
  | 10 => masksL10 n
  | 11 => masksL11 n
  | 12 => masksL12 n
  | 13 => masksL13 n
  | 14 => masksL14 n
  | 15 => masksL15 n
  | 16 => masksL16 n
  | 17 => masksL17 n
  | 18 => masksL18 n
  | 19 => masksL19 n
  | 20 => masksL20 n
  | 21 => masksL21 n
  | 22 => masksL22 n
  | 23 => masksL23 n
  | 24 => masksL24 n
  | 25 => masksL25 n
  | 26 => masksL26 n
  | 27 => masksL27 n
  | 28 => masksL28 n
  | 29 => masksL29 n
  | 30 => masksL30 n
  | 31 => masksL31 n
  | _ => []

theorem left_checked (i : Fin 12) (k : Fin 32) :
    gather (leftStart k.val) (3+i.val) [leftStart k.val]=
      leftMasks k.val (3+i.val) := by
  fin_cases k
  · exact checkedL0 i
  · exact checkedL1 i
  · exact checkedL2 i
  · exact checkedL3 i
  · exact checkedL4 i
  · exact checkedL5 i
  · exact checkedL6 i
  · exact checkedL7 i
  · exact checkedL8 i
  · exact checkedL9 i
  · exact checkedL10 i
  · exact checkedL11 i
  · exact checkedL12 i
  · exact checkedL13 i
  · exact checkedL14 i
  · exact checkedL15 i
  · exact checkedL16 i
  · exact checkedL17 i
  · exact checkedL18 i
  · exact checkedL19 i
  · exact checkedL20 i
  · exact checkedL21 i
  · exact checkedL22 i
  · exact checkedL23 i
  · exact checkedL24 i
  · exact checkedL25 i
  · exact checkedL26 i
  · exact checkedL27 i
  · exact checkedL28 i
  · exact checkedL29 i
  · exact checkedL30 i
  · exact checkedL31 i

def cachedStarts (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | k+1 => cachedStarts n k ++ (upperMasks k n ++ leftMasks k n)

def allMasks (n : ℕ) : List ℕ := cachedStarts n 32

theorem allMasks_eq_gatherStarts (i : Fin 12) :
    allMasks (3+i.val)=gatherStarts (3+i.val) 32 := by
  have h : ∀k ≤ 32,cachedStarts (3+i.val) k=gatherStarts (3+i.val) k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      simp only [cachedStarts,gatherStarts,ih (by omega)]
      rw [upper_checked i ⟨k,by omega⟩,left_checked i ⟨k,by omega⟩]
  exact h 32 le_rfl

theorem catalogCount_eq_allMasks (root : List Vertex) (i : Fin 12) :
    ShortRootRepresentatives.catalogCount root.toFinset (3+i.val)=
      hitCount (pack root) (allMasks (3+i.val)) := by
  rw [catalogCount_eq_gatherStarts,allMasks_eq_gatherStarts]

end RootedKP.CachedPaths
