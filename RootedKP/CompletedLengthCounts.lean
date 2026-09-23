import RootedKP.EvenLongCounts
import RootedKP.GlobalOddCounts
import RootedKP.LongPathCounting

namespace RootedKP.AKLT
open Honeycomb BoundaryCounts Arithmetic
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem odd_root_family_count {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    {n : ℕ} (hn : n≤20) (hodd : n%2=1) (T : Finset (Polymer F))
    (hT : ∀ q ∈ T,q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) :
    7*T.card ≤ p.length*cornerCount n := by
  by_cases hsmall : p.length≤41
  · have hh := odd_small_root_family_count p hsmall hn hodd T hT
    exact (Nat.mul_le_mul_left 7 hh).trans (Nat.mul_le_mul_right _ hp)
  · have hh := global_odd_family_count hn hodd T
      (fun q hq => ⟨(hT q hq).1,(hT q hq).2.1⟩)
    calc
      7*T.card ≤ 7*(6*cornerCount n) := Nat.mul_le_mul_left 7 hh
      _ = 42*cornerCount n := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem counted_path_spec {F : Rectangle} (p : Polymer F) (i : ℕ) (q : Polymer F)
    (hq : q ∈ (shortPathSet p).filter (fun q => q.length=3+i)) :
    q.kind=.path ∧ q.length=3+i ∧ Polymer.Incompatible p q := by
  obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
  have hk := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  exact ⟨hk.1,hn,(Polymer.incompatible_symm q p).mp hk.2⟩

theorem odd_count_lookup {n : ℕ} (hmin : 3≤n) (hmax : n≤20) (hodd : n%2=1) :
    cornerCount n = oddCounts[(n-3)/2]?.getD 0 := by
  have h : n=3 ∨ n=5 ∨ n=7 ∨ n=9 ∨ n=11 ∨ n=13 ∨ n=15 ∨ n=17 ∨ n=19 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [oddCounts,cornerCount_three,cornerCount_five,cornerCount_seven,
      cornerCount_nine,cornerCount_eleven,cornerCount_thirteen,Q15,Q17,Q19]

theorem even_count_lookup {n : ℕ} (hmin : 8≤n) (hmax : n≤20) (heven : n%2=0) :
    sideCount n = evenCountsFrom8[(n-8)/2]?.getD 0 := by
  have h : n=8 ∨ n=10 ∨ n=12 ∨ n=14 ∨ n=16 ∨ n=18 ∨ n=20 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [evenCountsFrom8,sideCount_eight,sideCount_ten,sideCount_twelve,
      sideCount_fourteen,R16,R18,R20]

theorem long_odd_length_bound {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    (i : ℕ) (hi : i<18) (hodd : (3+i)%2=1) :
    (pathLengthCount p i : ℝ) ≤ (p.length : ℝ)*(longCountCoefficient (3+i) : ℝ) := by
  have hn := odd_root_family_count p hp (show 3+i≤20 by omega) hodd
    ((shortPathSet p).filter (fun q => q.length=3+i)) (counted_path_spec p i)
  have hh : (7:ℝ)*(pathLengthCount p i : ℝ) ≤ (p.length : ℝ)*(cornerCount (3+i) : ℝ) := by
    exact_mod_cast hn
  rw [odd_count_lookup (by omega) (by omega) hodd] at hh
  have h4 : 3+i≠4 := by omega
  have h6 : 3+i≠6 := by omega
  simp only [longCountCoefficient,if_neg h4,if_neg h6,if_pos hodd,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_ofNat]
  nlinarith

theorem collarCoefficient_cast {n : ℕ} (hn : 8≤n) :
    ((n-1+6*(n/4-1) : ℕ) : ℝ) = (collarCoefficient n : ℝ) := by
  unfold collarCoefficient
  rw [Nat.cast_add,Nat.cast_sub (by omega : 1≤n),Nat.cast_mul,
    Nat.cast_sub (by omega : 1≤n/4)]
  push_cast
  ring

theorem long_even_length_bound {F : Rectangle} (p : Polymer F) (hp : 7≤p.length)
    (i : ℕ) (hi : i<18) (hmin : 8≤3+i) (heven : (3+i)%2=0) :
    (pathLengthCount p i : ℝ) ≤ (p.length : ℝ)*(longCountCoefficient (3+i) : ℝ) := by
  have hn := even_root_family_count p hmin (show 3+i≤20 by omega) heven
    ((shortPathSet p).filter (fun q => q.length=3+i)) (counted_path_spec p i)
  have hh : (2:ℝ)*(pathLengthCount p i : ℝ) ≤
      ((p.length : ℝ)+2*((3+i-1+6*((3+i)/4-1) : ℕ):ℝ))*(sideCount (3+i):ℝ) := by
    exact_mod_cast hn
  rw [collarCoefficient_cast hmin] at hh
  have hc : 0≤(collarCoefficient (3+i):ℝ) := by
    rw [←collarCoefficient_cast hmin]
    positivity
  have hplen : (7:ℝ)≤p.length := by exact_mod_cast hp
  have hcoef : (p.length:ℝ)/2+(collarCoefficient (3+i):ℝ) ≤
      (p.length:ℝ)*(1/2+(collarCoefficient (3+i):ℝ)/7) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hplen) hc]
  have hb : (pathLengthCount p i:ℝ) ≤
      ((p.length:ℝ)/2+(collarCoefficient (3+i):ℝ))*(sideCount (3+i):ℝ) := by nlinarith
  have hh' := hb.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _))
  rw [even_count_lookup hmin (by omega) heven] at hh'
  have h4 : 3+i≠4 := by omega
  have h6 : 3+i≠6 := by omega
  have ho : ¬(3+i)%2=1 := by omega
  simpa only [longCountCoefficient,if_neg h4,if_neg h6,if_neg ho,Rat.cast_mul,
    Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,mul_assoc] using hh'

end
end RootedKP.AKLT
