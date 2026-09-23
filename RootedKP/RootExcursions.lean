import RootedKP.TraceDecomposition
import RootedKP.CollarVertices

namespace RootedKP.Honeycomb

/-- Actual retained core vertices of the closed collar. -/
def Ring (F : Rectangle) (d : ℕ) (v : Vertex) : Prop :=
  Core F 200 v ∧ ¬ Core F (200-(d+1)) v

theorem WalkOn.mono {P Q : Vertex → Prop} {u v : Vertex} {n : ℕ}
    (h : WalkOn P u v n) (hPQ : ∀ w,P w→Q w) : WalkOn Q u v n := by
  induction h with
  | nil u hu => exact WalkOn.nil u (hPQ u hu)
  | cons hu he _ ih => exact WalkOn.cons (hPQ _ hu) he ih

theorem ring_edge_collar {F : Rectangle} {d : ℕ} {u v : Vertex}
    (hu : Ring F d u) (hv : Ring F d v) (he : Adj u v) : CollarEdge F 200 d u v :=
  ⟨⟨he,Or.inl hu.1⟩,(fun h => h.2.elim hu.2 hv.2),hu.1,hv.1⟩

/-- Exact excursion accounting for an actual outer-core trace starting in
the ring, using the proved boundary replacement for every short gap. -/
theorem ring_trace_excursion_cover {F : Rectangle} {d K : ℕ} (hd : d ≤ 4) (hK : K ≤ 86)
    {u v : Vertex} {n : ℕ} {S : Finset Vertex} (h : TracedWalk Adj u v n S)
    (hcore : ∀ w∈S,Core F 200 w) (hu : Ring F d u) : ExcursionCover (Ring F d) K u n S := by
  refine traced_excursion_cover (Ring F d) (InnerBoundary F d) K ?_ h hu ?_
  · intro a b m ha hb hw hm
    obtain ⟨m',hlen,hwalk⟩ := BoundaryCycle.short_walk_boundary_replacement hd ha hb hw (by omega)
    have hr := hwalk.mono (fun w hw => inner_vertex_core_ring hd hw)
    obtain ⟨T,hT,hregion⟩ := hr.traced
    exact ⟨⟨a,b,m',T,hT,hregion⟩,rfl,rfl,hlen⟩
  · intro a ha b hb he har hbr
    have hbdeep : Core F (200-(d+1)) b := by
      by_contra hn
      exact hbr ⟨hcore b hb,hn⟩
    exact ring_to_deep_on_inner hd har.2 hbdeep he

/-- A list of actual ring walks covers every ring contact of an arbitrary
outer-core trace. The charge for all additional pieces comes from removed
long excursions; the bound is derived from the original trace length. -/
theorem core_trace_ring_cover {F : Rectangle} {d K : ℕ} (hd : d ≤ 4) (hK : K ≤ 86)
    {u v : Vertex} {n : ℕ} {S : Finset Vertex} (h : TracedWalk Adj u v n S)
    (hcore : ∀ w∈S,Core F 200 w) :
    ∃ parts : List (TracePiece (Ring F d)),
      (parts.map TracePiece.length).sum + K*parts.length ≤ n+K ∧
      ∀ w∈S,Ring F d w→∃ p∈parts,w∈p.support := by
  classical
  rcases h.first_hit (Ring F d) with hnone | ⟨c,k,m,T,U,hT,hU,hkm,hSU,hc,honly⟩
  · refine ⟨[],by simp,?_⟩
    intro w hw hp
    exact False.elim (hnone w hw hp)
  · have hUcore : ∀ w∈U,Core F 200 w := by
      intro w hw
      apply hcore w
      rw [← hSU]
      exact Finset.mem_union_right _ hw
    obtain ⟨first,rest,hfirst,hbudget,hcover⟩ := ring_trace_excursion_cover hd hK hU hUcore hc
    refine ⟨first::rest,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · intro w hw hp
      rw [← hSU] at hw
      rcases Finset.mem_union.mp hw with hw | hw
      · have heq := honly w hw hp
        refine ⟨first,by simp,?_⟩
        exact heq.symm ▸ (hfirst ▸ first.trace.start_mem)
      · rcases hcover w hw hp with hw | ⟨p,hp',hw⟩
        · exact ⟨first,by simp,hw⟩
        · exact ⟨p,by simp [hp'],hw⟩

end RootedKP.Honeycomb
