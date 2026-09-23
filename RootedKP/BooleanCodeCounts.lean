import RootedKP.CodeCountCertificates

namespace RootedKP.CachedPaths
set_option maxHeartbeats 0

def booleanContains (i : ℕ) : List ℕ → Bool
  | [] => false
  | j::js => if Nat.blt i j then false else if Nat.beq i j then true else booleanContains i js

theorem booleanContains_eq (i : ℕ) (ys : List ℕ) :
    booleanContains i ys=orderedContains i ys := by
  induction ys with
  | nil => rfl
  | cons j js ih => simp [booleanContains,orderedContains,ih]

def booleanHitCount (codes : List ℕ) (paths : List (List ℕ)) : ℕ :=
  paths.countP (fun ys => codes.any (fun i => booleanContains i ys))

theorem booleanHitCount_eq (codes : List ℕ) (paths : List (List ℕ)) :
    booleanHitCount codes paths=codeHitCount codes paths := by
  have hf : (fun ys => codes.any (fun i => booleanContains i ys))=codeListHit codes := by
    funext ys
    simp only [booleanContains_eq]
    rfl
  rw [booleanHitCount,codeHitCount,hf]

def booleanCountByStarts (codes : List ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => booleanCountByStarts codes n k+
      (booleanHitCount codes (upperCodes k n)+booleanHitCount codes (leftCodes k n))

theorem booleanCountByStarts_eq (codes : List ℕ) (n k : ℕ) :
    booleanCountByStarts codes n k=codeCountByStarts codes n k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [booleanCountByStarts,codeCountByStarts,ih,booleanHitCount_eq]

end RootedKP.CachedPaths
