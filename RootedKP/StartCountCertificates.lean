import RootedKP.PathCache.All
import RootedKP.ArithmeticHits

namespace RootedKP.CachedPaths
open scoped BigOperators
set_option maxHeartbeats 0

/-- Count separately at each leaf, so the kernel need not normalize a long
concatenation repeatedly. The following identity proves this exact. -/
def countByStarts (codes : List ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => countByStarts codes n k+
      (arithmeticHitCount codes (upperMasks k n)+arithmeticHitCount codes (leftMasks k n))

theorem countByStarts_eq (codes : List ℕ) (n k : ℕ) :
    countByStarts codes n k=arithmeticHitCount codes (cachedStarts n k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [countByStarts,cachedStarts,ih,arithmeticHitCount,List.countP_append]

def splitCertificateChecked (bounds : List ℕ) (cert : List ℕ × (ℕ × List ℕ)) : Prop :=
  codeMask cert.1=cert.2.1 ∧
    (List.range 12).map (fun i => countByStarts cert.1 (3+i) 32)=cert.2.2 ∧
    ∀k : Fin 13,(∑i∈Finset.range k.val,cert.2.2[i]?.getD 0)≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0

instance (bounds : List ℕ) (cert : List ℕ × (ℕ × List ℕ)) :
    Decidable (splitCertificateChecked bounds cert) := by
  unfold splitCertificateChecked
  infer_instance

theorem rowChecked_of_splitCertificate (bounds : List ℕ)
    (cert : List ℕ × (ℕ × List ℕ)) (h : splitCertificateChecked bounds cert) :
    rowChecked allMasks bounds cert.2 := by
  obtain ⟨hm,hcounts,hprefix⟩ := h
  apply rowChecked_of_certificate allMasks bounds cert
  refine ⟨hm,?_,hprefix⟩
  simpa only [countByStarts_eq,allMasks] using hcounts

end RootedKP.CachedPaths
