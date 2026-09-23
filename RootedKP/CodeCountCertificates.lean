import RootedKP.CodeCache.All

namespace RootedKP.CachedPaths
open scoped BigOperators
set_option maxHeartbeats 0

def codeCertificateChecked (bounds : List ℕ) (cert : List ℕ × (ℕ × List ℕ)) : Prop :=
  codeMask cert.1=cert.2.1 ∧
    (List.range 12).map (fun i => codeCountByStarts cert.1 (3+i) 32)=cert.2.2 ∧
    ∀k : Fin 13,(∑i∈Finset.range k.val,cert.2.2[i]?.getD 0)≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0

instance (bounds : List ℕ) (cert : List ℕ × (ℕ × List ℕ)) :
    Decidable (codeCertificateChecked bounds cert) := by
  unfold codeCertificateChecked
  infer_instance

theorem rowChecked_of_codeCertificate (bounds : List ℕ)
    (cert : List ℕ × (ℕ × List ℕ)) (h : codeCertificateChecked bounds cert) :
    rowChecked allMasks bounds cert.2 := by
  obtain ⟨hm,hcounts,hprefix⟩ := h
  refine ⟨?_,hprefix⟩
  rw [←hcounts]
  unfold countVector
  apply List.map_congr_left
  intro i hi
  have heq := codeCountByStarts_eq cert.1 ⟨i,List.mem_range.mp hi⟩ 32 le_rfl
  simpa only [hm,allMasks] using heq.symm

end RootedKP.CachedPaths
