import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-! A weak walk on an integer circle occupies an arc no longer than the
walk. Contacts at distance at most r enlarge the arc by at most 2r. The
normalization uses a cut in (0,P], so both representations 0 and P of the
same boundary joint are treated consistently. -/
namespace RootedKP.CircleArcs

def Near (P r x y : ℤ) : Prop :=
  ∃ δ : ℤ, -r ≤ δ ∧ δ ≤ r ∧ Int.ModEq P (x + δ) y

theorem Near.refl (P x : ℤ) : Near P 0 x x :=
  ⟨0, le_rfl, le_rfl, by simp [Int.ModEq]⟩

theorem Near.mono {P r s x y : ℤ} (h : Near P r x y) (hrs : r ≤ s) :
    Near P s x y := by
  obtain ⟨δ,hd0,hd1,hd⟩ := h
  exact ⟨δ,by omega,by omega,hd⟩

theorem Near.symm {P r x y : ℤ} (h : Near P r x y) : Near P r y x := by
  obtain ⟨δ,hd0,hd1,hd⟩ := h
  refine ⟨-δ,by omega,by omega,?_⟩
  simpa [sub_eq_add_neg] using hd.symm.sub_right δ

theorem Near.trans {P r s x y z : ℤ} (h : Near P r x y) (h' : Near P s y z) :
    Near P (r+s) x z := by
  obtain ⟨δ,hd0,hd1,hd⟩ := h
  obtain ⟨ε,he0,he1,he⟩ := h'
  refine ⟨δ+ε,by omega,by omega,?_⟩
  simpa [add_assoc] using (hd.add_right ε).trans he

theorem Near.mod_right {P r x y z : ℤ} (h : Near P r x y) (he : Int.ModEq P y z) :
    Near P r x z := by
  obtain ⟨δ,hd0,hd1,hd⟩ := h
  exact ⟨δ,hd0,hd1,hd.trans he⟩

theorem indexed_near {P : ℤ} {f : ℕ → ℤ} {n : ℕ}
    (h : ∀ i < n, Near P 1 (f i) (f (i+1))) (i k : ℕ) (hik : i+k ≤ n) :
    Near P k (f i) (f (i+k)) := by
  induction k generalizing i with
  | zero => simpa using Near.refl P (f i)
  | succ k ih =>
    have hh := (h i (by omega)).trans (ih (i+1) (by omega))
    simpa [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh

def Trace (P : ℤ) : List ℤ → Prop
  | [] => True
  | [_] => True
  | u :: v :: vs => Near P 1 u v ∧ Trace P (v :: vs)

def Covered (P lo hi : ℤ) (xs : List ℤ) : Prop :=
  ∀ x ∈ xs, ∃ z : ℤ, Int.ModEq P x z ∧ lo ≤ z ∧ z ≤ hi

theorem trace_interval (P : ℤ) {xs : List ℤ} (h : Trace P xs) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ hi - lo ≤ (xs.length - 1 : ℕ) ∧ Covered P lo hi xs := by
  induction xs with
  | nil => exact ⟨0, 0, le_rfl, by simp, by simp [Covered]⟩
  | cons u vs ih =>
    cases vs with
    | nil =>
      refine ⟨u, u, le_rfl, by simp, ?_⟩
      intro x hx
      have hx' : x = u := by simpa using hx
      subst x
      exact ⟨u, Int.ModEq.rfl, le_rfl, le_rfl⟩
    | cons v vs =>
      obtain ⟨lo, hi, horder, hlen, hcover⟩ := ih h.2
      obtain ⟨z, hz, hzlo, hzhi⟩ := hcover v (by simp)
      obtain ⟨δ, hdlo, hdhi, hd⟩ := h.1
      have hu : Int.ModEq P u (z - δ) := by
        simpa using (hd.trans hz).sub_right δ
      refine ⟨min lo (z-δ), max hi (z-δ), ?_, ?_, ?_⟩
      · omega
      · simp only [List.length_cons] at hlen ⊢
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨z-δ, hu, min_le_right .., le_max_right ..⟩
        · obtain ⟨w, hw, hwlo, hwhi⟩ := hcover x hx
          exact ⟨w, hw, le_trans (min_le_left ..) hwlo,
            le_trans hwhi (le_max_left ..)⟩

theorem padded_contact {P lo hi r x y : ℤ} {xs : List ℤ}
    (hcover : Covered P lo hi xs) (hx : x ∈ xs) (hnear : Near P r x y) :
    ∃ z : ℤ, Int.ModEq P y z ∧ lo-r ≤ z ∧ z ≤ hi+r := by
  obtain ⟨w, hw, hwlo, hwhi⟩ := hcover x hx
  obtain ⟨δ, hdlo, hdhi, hd⟩ := hnear
  refine ⟨w+δ, hd.symm.trans (hw.add_right δ), ?_, ?_⟩ <;> omega

def liftAt (P cut x : ℤ) : ℤ := if x < cut then x + P else x

theorem liftAt_range {P cut x : ℤ} (hc : 0 < cut ∧ cut ≤ P)
    (hx : 0 ≤ x ∧ x ≤ P) : cut ≤ liftAt P cut x ∧ liftAt P cut x < cut+P := by
  unfold liftAt
  split_ifs <;> omega

theorem liftAt_modEq (P cut x : ℤ) : Int.ModEq P (liftAt P cut x) x := by
  unfold liftAt
  split_ifs <;> simp [Int.ModEq]

theorem modEq_unique {P cut x y : ℤ}
    (hx : cut ≤ x ∧ x < cut+P) (hy : cut ≤ y ∧ y < cut+P)
    (he : Int.ModEq P x y) : x = y := by
  have h := he.sub_right cut
  change (x-cut) % P = (y-cut) % P at h
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

theorem normalize_covered {P lo hi : ℤ} (hP : 0 < P) (horder : lo ≤ hi)
    (hshort : hi-lo < P) :
    ∃ cut : ℤ, 0 < cut ∧ cut ≤ P ∧
      ∀ x : ℤ, 0 ≤ x → x ≤ P →
        (∃ z : ℤ, Int.ModEq P x z ∧ lo ≤ z ∧ z ≤ hi) →
        cut ≤ liftAt P cut x ∧ liftAt P cut x ≤ cut+(hi-lo) := by
  let cut := (lo-1) % P + 1
  have hc : 0 < cut ∧ cut ≤ P := by
    have h0 := Int.emod_nonneg (lo-1) (ne_of_gt hP)
    have h1 := Int.emod_lt_of_pos (lo-1) hP
    dsimp [cut]
    omega
  have hmod : Int.ModEq P cut lo := by
    simpa [cut] using (Int.mod_modEq (lo-1) P).add_right 1
  refine ⟨cut, hc.1, hc.2, ?_⟩
  intro x hx0 hxP hex
  obtain ⟨z, hxz, hzlo, hzhi⟩ := hex
  have hr : cut ≤ cut+(z-lo) ∧ cut+(z-lo) < cut+P := by omega
  have he : Int.ModEq P (liftAt P cut x) (cut+(z-lo)) := by
    have hz : Int.ModEq P z (cut+(z-lo)) := by
      simpa using (hmod.symm.add_right (z-lo))
    exact (liftAt_modEq P cut x).trans (hxz.trans hz)
  have heq := modEq_unique (liftAt_range hc ⟨hx0,hxP⟩) hr he
  rw [heq]
  constructor <;> omega

/-- A single cut simultaneously unwraps every contact in the padded trace.
The sole length restriction is that the padded arc is shorter than the circle. -/
theorem trace_contacts_arc {P r : ℤ} {xs : List ℤ} (hP : 0 < P) (hr : 0 ≤ r)
    (htrace : Trace P xs) (hshort : (xs.length-1 : ℕ) + 2*r < P) :
    ∃ cut lo hi : ℤ, 0 < cut ∧ cut ≤ P ∧ lo ≤ hi ∧
      hi-lo ≤ (xs.length-1 : ℕ) + 2*r ∧
      ∀ y : ℤ, 0 ≤ y → y ≤ P →
        (∃ x ∈ xs, Near P r x y) →
        lo ≤ liftAt P cut y ∧ liftAt P cut y ≤ hi := by
  obtain ⟨a,b,hab,hlen,hcover⟩ := trace_interval P htrace
  obtain ⟨cut,hc0,hcP,hnorm⟩ := normalize_covered hP
    (show a-r ≤ b+r by omega) (show (b+r)-(a-r) < P by omega)
  refine ⟨cut,cut,cut+((b+r)-(a-r)),hc0,hcP,?_,?_,?_⟩
  · omega
  · omega
  · intro y hy0 hyP hcontact
    obtain ⟨x,hx,hnear⟩ := hcontact
    exact hnorm y hy0 hyP (padded_contact hcover hx hnear)

end RootedKP.CircleArcs
