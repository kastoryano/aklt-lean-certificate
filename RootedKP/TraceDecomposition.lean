import RootedKP.InnerBoundaryGeodesic
import Mathlib.Data.Finset.Union

namespace RootedKP.Honeycomb

/-- A finite walk together with its exact visited-vertex set. -/
inductive TracedWalk (E : Vertex → Vertex → Prop) : Vertex → Vertex → ℕ → Finset Vertex → Prop
  | nil (v : Vertex) : TracedWalk E v v 0 {v}
  | cons {u v w : Vertex} {n : ℕ} {S : Finset Vertex}
      (he : E u v) (tail : TracedWalk E v w n S) : TracedWalk E u w (n+1) (insert u S)

namespace TracedWalk
variable {E : Vertex → Vertex → Prop}

theorem start_mem {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk E u v n S) : u ∈ S := by
  cases h with
  | nil => simp
  | cons => simp

theorem finish_mem {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk E u v n S) : v ∈ S := by
  induction h with
  | nil => simp
  | cons _ _ ih => exact Finset.mem_insert_of_mem ih

theorem append {u v w : Vertex} {n m : ℕ} {S T : Finset Vertex}
    (h : TracedWalk E u v n S) (h' : TracedWalk E v w m T) :
    TracedWalk E u w (n+m) (S ∪ T) := by
  induction h with
  | nil v => simpa [h'.start_mem] using h'
  | cons he _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Finset.insert_union] using
      TracedWalk.cons he (ih h')

theorem toWalk {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk Adj u v n S) : Walk u v n := by
  induction h with
  | nil v => exact Walk.nil v
  | cons he _ ih => exact Walk.cons he ih

theorem last_edge {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk E u v n S) (hn : 0 < n) : ∃ w ∈ S, E w v := by
  induction h with
  | nil => omega
  | @cons u v w n S he ht ih =>
    cases n with
    | zero => cases ht; exact ⟨u, by simp, he⟩
    | succ n =>
      obtain ⟨z,hz,he⟩ := ih (by omega)
      exact ⟨z,Finset.mem_insert_of_mem hz,he⟩

/-- Stop at the first vertex satisfying `P`; all earlier visited vertices
fail `P`. The remainder retains its exact length and visited set. -/
theorem first_hit (P : Vertex → Prop) {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk E u v n S) :
    (∀ w ∈ S, ¬ P w) ∨
    ∃ c k m T U, TracedWalk E u c k T ∧ TracedWalk E c v m U ∧
      k+m=n ∧ T∪U=S ∧ P c ∧ ∀ w ∈ T, P w → w=c := by
  classical
  induction h with
  | nil v =>
    by_cases hv : P v
    · exact Or.inr ⟨v,0,0,{v},{v},TracedWalk.nil v,TracedWalk.nil v,rfl,by simp,hv,by simp⟩
    · exact Or.inl (by simpa using hv)
  | @cons u v w n S he ht ih =>
    by_cases hu : P u
    · exact Or.inr ⟨u,0,n+1,{u},insert u S,TracedWalk.nil u,TracedWalk.cons he ht,
        by omega,by simp,hu,by simp⟩
    · rcases ih with hnone | ⟨c,k,m,T,U,hT,hU,hkm,hSU,hc,honly⟩
      · left
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hu
        · exact hnone z hz
      · right
        refine ⟨c,k+1,m,insert u T,U,TracedWalk.cons he hT,hU,by omega,?_,hc,?_⟩
        · simpa [Finset.insert_union] using congrArg (insert u) hSU
        · intro z hz hp
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact False.elim (hu hp)
          · exact honly z hz hp

/-- Recover a literal list with exactly the recorded visited set and length. -/
theorem asList {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk E u v n S) :
    ∃ vs : List Vertex, vs.head?=some u ∧ vs.getLast?=some v ∧
      vs.length=n+1 ∧ vs.toFinset=S ∧ ListWalk E vs := by
  induction h with
  | nil u => exact ⟨[u],rfl,rfl,rfl,by simp,trivial⟩
  | @cons u v w n S he ht ih =>
    obtain ⟨vs,hh,hl,hlen,hset,hw⟩ := ih
    cases vs with
    | nil => simp at hh
    | cons a rest =>
      have ha : a=v := by simpa using hh
      subst a
      refine ⟨u::v::rest,rfl,?_,by simp at hlen ⊢; omega,?_,he,hw⟩
      · simpa using hl
      · simpa [hset]

theorem onRegion {P : Vertex → Prop} {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk Adj u v n S) (hP : ∀ w∈S,P w) : WalkOn P u v n := by
  induction h with
  | nil u => exact WalkOn.nil u (hP u (by simp))
  | cons he ht ih => exact WalkOn.cons (hP _ (by simp)) he (ih (fun w hw => hP w (Finset.mem_insert_of_mem hw)))

end TracedWalk

/-- Each retained component is an actual walk in the chosen vertex region. -/
structure TracePiece (P : Vertex → Prop) where
  start : Vertex
  finish : Vertex
  length : ℕ
  support : Finset Vertex
  trace : TracedWalk Adj start finish length support
  in_region : ∀ v ∈ support, P v

namespace TracePiece
variable {P : Vertex → Prop}

def singleton (u : Vertex) (hu : P u) : TracePiece P :=
  ⟨u,u,0,{u},TracedWalk.nil u,by simpa using hu⟩

def join (p q : TracePiece P) (h : p.finish = q.start) : TracePiece P := {
  start := p.start
  finish := q.finish
  length := p.length+q.length
  support := p.support∪q.support
  trace := p.trace.append (h ▸ q.trace)
  in_region := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (p.in_region v) (q.in_region v)
}

end TracePiece

/-- A first component beginning at the root's first vertex, plus any
components separated by removed long excursions. Every ring contact stays. -/
def ExcursionCover (P : Vertex → Prop) (K : ℕ) (u : Vertex) (n : ℕ) (S : Finset Vertex) : Prop :=
  ∃ first : TracePiece P, ∃ rest : List (TracePiece P), first.start=u ∧
    first.length + (rest.map TracePiece.length).sum + K*rest.length ≤ n ∧
    ∀ v ∈ S, P v → v ∈ first.support ∨ ∃ p ∈ rest, v ∈ p.support

/-- A region-constrained walk supplies an actual trace with exact length. -/
theorem WalkOn.traced {P : Vertex → Prop} {u v : Vertex} {n : ℕ}
    (h : WalkOn P u v n) : ∃ S, TracedWalk Adj u v n S ∧ ∀ w ∈ S, P w := by
  induction h with
  | nil u hu => exact ⟨{u},TracedWalk.nil u,by simpa using hu⟩
  | @cons u v w n hu he ht ih =>
    obtain ⟨S,hS,hP⟩ := ih
    refine ⟨insert u S,TracedWalk.cons he hS,?_⟩
    intro z hz
    exact (Finset.mem_insert.mp hz).elim (fun h => h ▸ hu) (hP z)

/-- An explicit first-return decomposition, including arbitrary interior
runs. Long gaps pay for additional components; short gaps are replaced by
actual region walks. No decomposition or length-budget assumption is used. -/
theorem traced_excursion_cover (P B : Vertex → Prop) (K : ℕ)
    (hreplace : ∀ u v n, B u → B v → Walk u v n → n ≤ K →
      ∃ p : TracePiece P, p.start=u ∧ p.finish=v ∧ p.length≤n)
    {u v : Vertex} {n : ℕ} {S : Finset Vertex}
    (h : TracedWalk Adj u v n S) (hu : P u)
    (hboundary : ∀ a ∈ S, ∀ b ∈ S, Adj a b → P a → ¬ P b → B a) :
    ExcursionCover P K u n S := by
  classical
  induction n using Nat.strong_induction_on generalizing u v S with
  | h n ih =>
    cases h with
    | nil u =>
      refine ⟨TracePiece.singleton u hu,[],rfl,by simp [TracePiece.singleton],?_⟩
      simp [TracePiece.singleton]
    | @cons u v w n S he ht =>
      by_cases hv : P v
      · obtain ⟨first,rest,hfirst,hbudget,hcover⟩ := ih n (by omega) ht hv
          (fun a ha b hb => hboundary a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
        let first' : TracePiece P := {
          start := u
          finish := first.finish
          length := first.length+1
          support := insert u first.support
          trace := TracedWalk.cons he (hfirst ▸ first.trace)
          in_region := by
            intro z hz
            exact (Finset.mem_insert.mp hz).elim (fun h => h ▸ hu) (first.in_region z)
        }
        refine ⟨first',rest,rfl,by dsimp [first']; omega,?_⟩
        intro z hz hp
        rcases Finset.mem_insert.mp hz with rfl | hz
        · left; exact Finset.mem_insert_self ..
        · rcases hcover z hz hp with hz | hz
          · left; exact Finset.mem_insert_of_mem hz
          · exact Or.inr hz
      · rcases ht.first_hit P with hnone | ⟨c,k,m,T,U,hT,hU,hkm,hSU,hc,honly⟩
        · refine ⟨TracePiece.singleton u hu,[],rfl,by simp [TracePiece.singleton],?_⟩
          intro z hz hp
          rcases Finset.mem_insert.mp hz with rfl | hz
          · left; simp [TracePiece.singleton]
          · exact False.elim (hnone z hz hp)
        · have hk : 0 < k := by
            cases k with
            | zero => cases hT; exact False.elim (hv hc)
            | succ k => omega
          have hbstart := hboundary u (Finset.mem_insert_self ..) v
            (Finset.mem_insert_of_mem ht.start_mem) he hu hv
          obtain ⟨z,hz,hzc⟩ := hT.last_edge hk
          have hznot : ¬ P z := by
            intro hp
            have heq := honly z hz hp
            exact adj_irrefl c (heq ▸ hzc)
          have hTsub : T ⊆ insert u S := by
            intro a ha
            apply Finset.mem_insert_of_mem
            rw [← hSU]
            exact Finset.mem_union_left _ ha
          have hUsub : U ⊆ insert u S := by
            intro a ha
            apply Finset.mem_insert_of_mem
            rw [← hSU]
            exact Finset.mem_union_right _ ha
          have hbfinish := hboundary c (hTsub hT.finish_mem) z (hTsub hz) (adj_symm hzc) hc hznot
          obtain ⟨first,rest,hfirst,hbudget,hcover⟩ := ih m (by omega) hU hc
            (fun a ha b hb => hboundary a (hUsub ha) b (hUsub hb))
          have hcfirst : c ∈ first.support := hfirst ▸ first.trace.start_mem
          have covered : ∀ z ∈ insert u S, P z →
              z=u ∨ z∈first.support ∨ ∃ p∈rest,z∈p.support := by
            intro z hz hp
            rcases Finset.mem_insert.mp hz with hz | hz
            · exact Or.inl hz
            · rw [← hSU] at hz
              rcases Finset.mem_union.mp hz with hz | hz
              · exact Or.inr (Or.inl ((honly z hz hp).symm ▸ hcfirst))
              · exact Or.inr (hcover z hz hp)
          by_cases hshort : k+1 ≤ K
          · obtain ⟨bridge,hpstart,hpfinish,hplen⟩ :=
              hreplace u c (k+1) hbstart hbfinish (TracedWalk.cons he hT).toWalk hshort
            let first' := bridge.join first (hpfinish.trans hfirst.symm)
            refine ⟨first',rest,hpstart,?_,?_⟩
            · dsimp [first',TracePiece.join]
              omega
            · intro z hz hp
              rcases covered z hz hp with rfl | hz | hz
              · left
                exact Finset.mem_union_left _ (hpstart ▸ bridge.trace.start_mem)
              · left; exact Finset.mem_union_right _ hz
              · exact Or.inr hz
          · refine ⟨TracePiece.singleton u hu,first::rest,rfl,?_,?_⟩
            · simp only [TracePiece.singleton, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
              omega
            · intro z hz hp
              rcases covered z hz hp with rfl | hz | ⟨p,hp',hz⟩
              · left; simp [TracePiece.singleton]
              · exact Or.inr ⟨first,by simp,hz⟩
              · exact Or.inr ⟨p,by simp [hp'],hz⟩

end RootedKP.Honeycomb
