import RootedKP.Honeycomb
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! All-size separation of nonadjacent halo sides in the exact dual metric. -/
namespace RootedKP.Honeycomb

/-- Signed distances to the six support lines in cyclic order. -/
def sideMargin (F : Rectangle) (s : ℕ) (f : Face) (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => F.qmax + s - f.1
  | 1 => F.qmax + F.rmax + s - (f.1 + f.2)
  | 2 => F.rmax + s - f.2
  | 3 => f.1 - (F.qmin - s)
  | 4 => f.1 + f.2 - (F.qmin + F.rmin - s)
  | _ => f.2 - (F.rmin - s)

def SideAdjacent (i j : Fin 6) : Prop :=
  (i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val

/-- The dual hex metric written without absolute-value notation. -/
def DualWithin (f g : Face) (L : ℕ) : Prop :=
  f.1 - g.1 ≤ L ∧ g.1 - f.1 ≤ L ∧
  f.2 - g.2 ≤ L ∧ g.2 - f.2 ≤ L ∧
  (f.1 + f.2) - (g.1 + g.2) ≤ L ∧ (g.1 + g.2) - (f.1 + f.2) ≤ L

theorem sideMargin_nonnegative {F : Rectangle} {s : ℕ} {f : Face}
    (hf : FaceHalo F s f) (i : Fin 6) : 0 ≤ sideMargin F s f i := by
  unfold FaceHalo at hf
  fin_cases i <;> simp only [sideMargin] <;> omega

/-- Two nonadjacent facets cannot both be close to an interior face. -/
theorem nonadjacent_margin_sum {F : Rectangle} {s : ℕ} {f : Face}
    (hf : FaceHalo F s f) (i j : Fin 6) (hne : i ≠ j)
    (hsep : ¬ SideAdjacent i j) :
    (s : ℤ) ≤ sideMargin F s f i + sideMargin F s f j := by
  have hq := F.q_order
  have hr := F.r_order
  unfold FaceHalo at hf
  fin_cases i <;> fin_cases j <;>
    norm_num [sideMargin, SideAdjacent] at * <;> omega

theorem sideMargin_lipschitz {F : Rectangle} {s L : ℕ} {f g : Face}
    (hfg : DualWithin f g L) (i : Fin 6) :
    sideMargin F s f i - sideMargin F s g i ≤ L ∧
      sideMargin F s g i - sideMargin F s f i ≤ L := by
  unfold DualWithin at hfg
  fin_cases i <;> simp only [sideMargin] <;> omega

/-- Actual points of two nonadjacent support sides are at least `s` dual
steps apart, uniformly in both dimensions of the original rectangle. -/
theorem nonadjacent_sides_separated {F : Rectangle} {s L : ℕ} {f g : Face}
    (hf : FaceHalo F s f) (i j : Fin 6) (hne : i ≠ j)
    (hsep : ¬ SideAdjacent i j)
    (hfi : sideMargin F s f i = 0) (hgj : sideMargin F s g j = 0)
    (hfg : DualWithin f g L) : s ≤ L := by
  have hsum := nonadjacent_margin_sum hf i j hne hsep
  have hdist := sideMargin_lipschitz (F := F) (s := s) hfg j
  omega

/-- In particular, a diameter-56 footprint cannot reach nonadjacent sides
of the radius-200 halo. It still takes chart construction to prove embedding
in the finite enumeration graph. -/
theorem radius200_no_nonadjacent_footprint {F : Rectangle} {f g : Face}
    (hf : FaceHalo F 200 f) (i j : Fin 6) (hne : i ≠ j)
    (hsep : ¬ SideAdjacent i j)
    (hfi : sideMargin F 200 f i = 0) (hgj : sideMargin F 200 g j = 0)
    (hfg : DualWithin f g 56) : False := by
  have := nonadjacent_sides_separated hf i j hne hsep hfi hgj hfg
  omega

/-- The same separation excludes nonadjacent inset sides for all short
interior excursions in the paper's collar argument. -/
theorem inset_no_nonadjacent_short_excursion {F : Rectangle} {d L : ℕ}
    (hd : d ≤ 4) (hL : L ≤ 86) {f g : Face}
    (hf : FaceHalo F (200 - d) f) (i j : Fin 6) (hne : i ≠ j)
    (hsep : ¬ SideAdjacent i j)
    (hfi : sideMargin F (200 - d) f i = 0)
    (hgj : sideMargin F (200 - d) g j = 0)
    (hfg : DualWithin f g L) : False := by
  have := nonadjacent_sides_separated hf i j hne hsep hfi hgj hfg
  omega

end RootedKP.Honeycomb
