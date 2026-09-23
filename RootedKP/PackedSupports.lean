import RootedKP.ShortRootCharts
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Encodable.Basic

namespace RootedKP.PackedSupports
open Honeycomb ShortRootCharts
set_option maxHeartbeats 0

/-- A globally injective vertex code: no coordinate cutoff is used. -/
def vertexCode : Vertex → ℕ
  | .a q r => 2*Nat.pair (Encodable.encode q) (Encodable.encode r)
  | .b q r => 2*Nat.pair (Encodable.encode q) (Encodable.encode r)+1

theorem vertexCode_injective : Function.Injective vertexCode := by
  intro u v h
  cases u <;> cases v <;> simp only [vertexCode] at h
  all_goals first
    | omega
    | rename_i q r q' r'
      have hp : Nat.pair (Encodable.encode q) (Encodable.encode r)=
          Nat.pair (Encodable.encode q') (Encodable.encode r') := by omega
      obtain ⟨hq,hr⟩ := Nat.pair_eq_pair.mp hp
      have hq' := Encodable.encode_injective hq
      have hr' := Encodable.encode_injective hr
      subst_vars
      rfl

def pack : List Vertex → ℕ
  | [] => 0
  | v::vs => 2^vertexCode v ||| pack vs

theorem testBit_pack (vs : List Vertex) (i : ℕ) :
    (pack vs).testBit i=decide (∃v∈vs,vertexCode v=i) := by
  induction vs with
  | nil => simp [pack]
  | cons v vs ih => simp [pack,Nat.testBit_lor,Nat.testBit_two_pow,ih]

theorem overlap_iff (xs ys : List Vertex) :
    pack xs &&& pack ys≠0 ↔ ∃v∈xs,v∈ys := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_land,testBit_pack,testBit_pack] at hi
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hi
    obtain ⟨⟨u,hu,huv⟩,v,hv,hvv⟩ := hi
    have heq := vertexCode_injective (huv.trans hvv.symm)
    exact ⟨u,hu,heq.symm ▸ hv⟩
  · rintro ⟨v,hx,hy⟩ hzero
    have hh : (pack xs &&& pack ys).testBit (vertexCode v)=true := by
      simp only [Nat.testBit_land,testBit_pack,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨⟨v,hx,rfl⟩,v,hy,rfl⟩
    simp [hzero] at hh

theorem overlap_hitsRoot (root trail : List Vertex) :
    pack root &&& pack trail≠0 ↔ hitsRoot root.toFinset trail := by
  simp only [overlap_iff,hitsRoot,List.mem_toFinset]

end RootedKP.PackedSupports
