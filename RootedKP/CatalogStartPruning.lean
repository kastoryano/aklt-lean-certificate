import RootedKP.ShortRootReduction

namespace RootedKP.ShortRootRepresentatives
open Honeycomb BoundaryCharts BoundaryCounts Enumeration ShortRootCharts
open scoped BigOperators
set_option maxHeartbeats 0

/-- A starting leaf must be close enough to at least one root vertex.
This only removes impossible starts; it does not truncate a search. -/
def rootStartPossible (root : Finset Vertex) (n : ℕ) (start : Vertex) : Prop :=
  ∃v∈root,reachesHeight heightQ (heightQ v) n start ∧ reachesHeight heightR (heightR v) n start

instance (root : Finset Vertex) (n : ℕ) (start : Vertex) :
    Decidable (rootStartPossible root n start) := by
  unfold rootStartPossible
  infer_instance

theorem root_start_necessary (root : Finset Vertex) (n : ℕ) (start : Vertex)
    (trail : List Vertex) (he : Extends (next .corner) n [start] trail)
    (ha : accepts root start trail) : rootStartPossible root n start := by
  obtain ⟨v,hv,hvt⟩ := ha.2
  have hq := extends_member_height .corner heightQ heightQ_lipschitz he hvt
  have hr := extends_member_height .corner heightR heightR_lipschitz he hvt
  exact ⟨v,hv,hq.symm,hr.symm⟩

def catalogStartCount (root : Finset Vertex) (n : ℕ) (start : Vertex) : ℕ :=
  if rootStartPossible root n start then
    prunedCount .corner (accepts root start) (endpointPossible .corner) n [start]
  else 0

theorem catalogStartCount_eq (root : Finset Vertex) (n : ℕ) (start : Vertex) :
    catalogStartCount root n start=
      prunedCount .corner (accepts root start) (endpointPossible .corner) n [start] := by
  unfold catalogStartCount
  split_ifs with h
  · rfl
  · symm
    rw [prunedCount_eq _ _ _ (accepted_endpoint_possible root start),fastCount_eq,
      LoopCounts.acceptedCount_eq_card,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro trail ht
    obtain ⟨he,ha⟩ := Finset.mem_filter.mp ht
    exact h (root_start_necessary root n start trail ((mem_extensions_iff _ _ _ _).mp he) ha)

/-- A faster executable form of the complete 64-start catalog counter. -/
def fastCatalogCount (root : Finset Vertex) (n : ℕ) : ℕ :=
  ∑start∈starts 62,catalogStartCount root n start

theorem fastCatalogCount_eq (root : Finset Vertex) (n : ℕ) :
    fastCatalogCount root n=catalogCount root n := by
  simp only [fastCatalogCount,catalogCount,catalogStartCount_eq]

end RootedKP.ShortRootRepresentatives
