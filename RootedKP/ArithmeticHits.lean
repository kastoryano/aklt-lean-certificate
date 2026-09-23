import RootedKP.CountRows

/-! The kernel can check intersections efficiently by testing the few bits
of the root support. The equivalence below removes any trust in this optimization. -/
namespace RootedKP.CachedPaths
open scoped BigOperators
set_option maxHeartbeats 0

def codeMask : List ℕ → ℕ
  | [] => 0
  | i::is => 2^i ||| codeMask is

theorem testBit_codeMask (cs : List ℕ) (i : ℕ) :
    (codeMask cs).testBit i=decide (i∈cs) := by
  induction cs with
  | nil => simp [codeMask]
  | cons c cs ih => simp [codeMask,Nat.testBit_two_pow,ih,eq_comm]

def arithmeticHit (codes : List ℕ) (mask : ℕ) : Bool :=
  codes.any (fun i => decide (mask/2^i%2=1))

theorem arithmeticHit_eq (codes : List ℕ) (mask : ℕ) :
    arithmeticHit codes mask=(codeMask codes &&& mask != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [arithmeticHit,List.any_eq_true,decide_eq_true_eq,bne_iff_ne]
  constructor
  · rintro ⟨i,hi,hbit⟩ hzero
    have hm : mask.testBit i=true := by
      simpa only [Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq] using hbit
    have hh : (codeMask codes &&& mask).testBit i=true := by
      simp [Nat.testBit_land,testBit_codeMask,hi,hm]
    simp [hzero] at hh
  · intro hne
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_land,testBit_codeMask] at hi
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    refine ⟨i,hi.1,?_⟩
    simpa only [Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq] using hi.2

def arithmeticHitCount (codes : List ℕ) (masks : List ℕ) : ℕ :=
  masks.countP (arithmeticHit codes)

theorem arithmeticHitCount_eq (codes : List ℕ) (masks : List ℕ) :
    arithmeticHitCount codes masks=hitCount (codeMask codes) masks := by
  have hf : arithmeticHit codes=(fun m => codeMask codes &&& m != 0) :=
    funext (arithmeticHit_eq codes)
  rw [arithmeticHitCount,hitCount,hf]

def certificateChecked (paths : ℕ → List ℕ) (bounds : List ℕ)
    (cert : List ℕ × (ℕ × List ℕ)) : Prop :=
  codeMask cert.1=cert.2.1 ∧
    (List.range 12).map (fun i => arithmeticHitCount cert.1 (paths (3+i)))=cert.2.2 ∧
    ∀k : Fin 13,(∑i∈Finset.range k.val,cert.2.2[i]?.getD 0)≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0

instance (paths : ℕ → List ℕ) (bounds : List ℕ) (cert : List ℕ × (ℕ × List ℕ)) :
    Decidable (certificateChecked paths bounds cert) := by
  unfold certificateChecked
  infer_instance

theorem rowChecked_of_certificate (paths : ℕ → List ℕ) (bounds : List ℕ)
    (cert : List ℕ × (ℕ × List ℕ)) (h : certificateChecked paths bounds cert) :
    rowChecked paths bounds cert.2 := by
  obtain ⟨hm,hcounts,hprefix⟩ := h
  refine ⟨?_,hprefix⟩
  simpa only [arithmeticHitCount_eq,hm,countVector] using hcounts

end RootedKP.CachedPaths
