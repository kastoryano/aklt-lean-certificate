import RootedKP.ArithmeticHits

namespace RootedKP.CachedPaths
set_option maxHeartbeats 0

def orderedContains (i : ℕ) : List ℕ → Bool
  | [] => false
  | j::js => if i<j then false else if i=j then true else orderedContains i js

theorem orderedContains_eq (i : ℕ) (ys : List ℕ) (hs : ys.Pairwise (· ≤ ·)) :
    orderedContains i ys=decide (i∈ys) := by
  induction ys with
  | nil => rfl
  | cons j js ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hlt : i<j
    · have hn : i∉j::js := by
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hin
        · omega
        · have := hhead i hin
          omega
      simp [orderedContains,hlt,hn]
    · by_cases heq : i=j
      · simp [orderedContains,hlt,heq]
      · simp [orderedContains,hlt,heq,ih htail]

def codeListHit (xs ys : List ℕ) : Bool := xs.any (fun i => orderedContains i ys)

theorem codeListHit_eq (xs ys : List ℕ) (hs : ys.Pairwise (· ≤ ·)) :
    codeListHit xs ys=(codeMask xs &&& codeMask ys != 0) := by
  rw [←arithmeticHit_eq]
  unfold codeListHit arithmeticHit
  apply congrArg (List.any xs)
  funext i
  rw [orderedContains_eq i ys hs,←Nat.testBit_eq_decide_div_mod_eq,testBit_codeMask]

def codeHitCount (codes : List ℕ) (paths : List (List ℕ)) : ℕ :=
  paths.countP (codeListHit codes)

theorem codeHitCount_eq (codes : List ℕ) (paths : List (List ℕ))
    (hs : ∀ys∈paths,ys.Pairwise (· ≤ ·)) :
    codeHitCount codes paths=hitCount (codeMask codes) (paths.map codeMask) := by
  unfold codeHitCount hitCount
  rw [List.countP_map]
  apply List.countP_congr
  intro ys hy
  simp only [codeListHit_eq codes ys (hs ys hy),Function.comp_apply]

end RootedKP.CachedPaths
