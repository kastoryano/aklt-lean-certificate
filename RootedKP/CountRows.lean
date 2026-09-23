import RootedKP.CachedPathEnumeration

namespace RootedKP.CachedPaths
open scoped BigOperators
set_option maxHeartbeats 0

def countVector (paths : ℕ → List ℕ) (r : ℕ) : List ℕ :=
  (List.range 12).map (fun i => hitCount r (paths (3+i)))

def rowChecked (paths : ℕ → List ℕ) (bounds : List ℕ) (row : ℕ × List ℕ) : Prop :=
  countVector paths row.1=row.2 ∧
    ∀k : Fin 13,(∑i∈Finset.range k.val,row.2[i]?.getD 0)≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0

instance (paths : ℕ → List ℕ) (bounds : List ℕ) (row : ℕ × List ℕ) :
    Decidable (rowChecked paths bounds row) := by unfold rowChecked; infer_instance

theorem countVector_lookup (paths : ℕ → List ℕ) (r i : ℕ) (hi : i < 12) :
    (countVector paths r)[i]?.getD 0=hitCount r (paths (3+i)) := by
  simp [countVector,List.getElem?_map,List.getElem?_range,hi]

theorem prefix_of_checked_row (paths : ℕ → List ℕ) (bounds : List ℕ)
    (row : ℕ × List ℕ) (h : rowChecked paths bounds row) (k : Fin 13) :
    (∑i∈Finset.range k.val,hitCount row.1 (paths (3+i)))≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0 := by
  obtain ⟨hvec,hprefix⟩ := h
  calc
    _ = ∑i∈Finset.range k.val,row.2[i]?.getD 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [←hvec,countVector_lookup paths row.1 i (by have := Finset.mem_range.mp hi; omega)]
    _ ≤ _ := hprefix k

theorem prefix_of_checked_rows (paths : ℕ → List ℕ) (bounds : List ℕ)
    (rows : List (ℕ × List ℕ)) (hc : ∀row∈rows,rowChecked paths bounds row)
    (r : ℕ) (hr : r∈rows.map Prod.fst) (k : Fin 13) :
    (∑i∈Finset.range k.val,hitCount r (paths (3+i)))≤
      ∑i∈Finset.range k.val,bounds[i]?.getD 0 := by
  obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hr
  exact prefix_of_checked_row paths bounds row (hc row hrow) k

end RootedKP.CachedPaths
