import RootedKP.RegionalEndpoints

/-!
# All-length endpoint growth from a finite-depth certificate

This version concerns the actual radius-200 regional sun graph.
Forgetting visited vertices only increases the accepted completion count.
This proved monotonicity supplies the endpoint recurrence; the recurrence is
not assumed. A uniform length-ten bound then propagates to every longer path.
-/
namespace RootedKP.RegionalEndpoints
open Honeycomb BoundaryCharts BoundaryCounts Enumeration LoopCounts
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

/-- Removing forbidden vertices from the visited tail can only increase the
number of completions ending in the specified vertex set. -/
theorem acceptedCount_visited_mono (F : Rectangle) (n : ℕ) (u : Vertex)
    (long short : List Vertex) (hsub : ∀ v ∈ short, v ∈ long) :
    acceptedCount (next F) (endsAt (Leaf F 200)) n (u :: long) ≤
      acceptedCount (next F) (endsAt (Leaf F 200)) n (u :: short) := by
  induction n generalizing u long short with
  | zero => simp only [acceptedCount, endsAt, le_refl]
  | succ n ih =>
    simp only [acceptedCount]
    have hchoices : (next F u).filter (fun v => v ∉ u :: long) ⊆
        (next F u).filter (fun v => v ∉ u :: short) := by
      intro v hv
      obtain ⟨hv,hnew⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨hv, ?_⟩
      intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hnew (List.mem_cons_self ..)
      · exact hnew (List.mem_cons_of_mem u (hsub v hm))
    calc
      _ ≤ ∑ v ∈ (next F u).filter (fun v => v ∉ u :: long),
          acceptedCount (next F) (endsAt (Leaf F 200)) n (v :: u :: short) := by
        apply Finset.sum_le_sum
        intro v _
        apply ih v (u :: long) (u :: short)
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem u (hsub w hw)
      _ ≤ _ := Finset.sum_le_sum_of_subset hchoices

/-- An accumulated simple trail imposes at least the exclusion imposed by the
fresh endpoint counter, which remembers only the previous vertex. -/
theorem acceptedCount_le_count (F : Rectangle) (n : ℕ) (u forbidden : Vertex)
    (rest : List Vertex) :
    acceptedCount (next F) (endsAt (Leaf F 200)) n (u :: forbidden :: rest) ≤
      count F n u forbidden := by
  cases n with
  | zero => simp only [acceptedCount, count, endsAt, le_refl]
  | succ n =>
    simp only [acceptedCount, count]
    have hchoices : (next F u).filter (fun v => v ∉ u :: forbidden :: rest) ⊆
        (next F u).erase forbidden := by
      intro v hv
      obtain ⟨hv,hnew⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_erase.mpr ⟨fun he => hnew (by simp [he]),hv⟩
    calc
      _ ≤ ∑ v ∈ (next F u).filter (fun v => v ∉ u :: forbidden :: rest),
          acceptedCount (next F) (endsAt (Leaf F 200)) n [v,u] := by
        apply Finset.sum_le_sum
        intro v _
        apply acceptedCount_visited_mono F n v (u :: forbidden :: rest) [u]
        intro w hw
        have he : w = u := List.mem_singleton.mp hw
        subst w
        exact List.mem_cons_self ..
      _ ≤ _ := Finset.sum_le_sum_of_subset hchoices

/-- The actual endpoint counter satisfies a one-step upper recurrence. -/
theorem count_succ_le (F : Rectangle) (n : ℕ) (u forbidden : Vertex) :
    count F (n+1) u forbidden ≤
      ∑ v ∈ (next F u).erase forbidden, count F n v u := by
  unfold count
  apply Finset.sum_le_sum
  intro v _
  exact acceptedCount_le_count F n v u []

/-- A uniform finite-depth bound propagates through at most two forward choices. -/
theorem count_growth (F : Rectangle) (m B : ℕ)
    (hbase : ∀ u forbidden, forbidden ∈ next F u → count F m u forbidden ≤ B)
    (j : ℕ) (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    count F (m+j) u forbidden ≤ 2 ^ j * B := by
  induction j generalizing u forbidden with
  | zero => simpa using hbase u forbidden hf
  | succ j ih =>
    have hchoices : ((next F u).erase forbidden).card ≤ 2 := by
      have hdeg : (next F u).card ≤ 3 :=
        (Finset.card_filter_le _ _).trans_eq (neighbors_card u)
      rw [Finset.card_erase_of_mem hf]
      omega
    calc
      _ ≤ ∑ v ∈ (next F u).erase forbidden, count F (m+j) v u :=
        count_succ_le F (m+j) u forbidden
      _ ≤ ∑ _v ∈ (next F u).erase forbidden, 2^j * B := by
        apply Finset.sum_le_sum
        intro v hv
        exact ih v u ((mem_next F v u).mpr
          (Honeycomb.sunAdj_symm ((mem_next F u v).mp (Finset.mem_erase.mp hv).2)))
      _ = ((next F u).erase forbidden).card * (2^j * B) := by simp
      _ ≤ 2 * (2^j * B) := Nat.mul_le_mul_right _ hchoices
      _ = 2^(j+1) * B := by simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The certified N10≤64 estimate entails N(k)≤2^(k−4) at every k≥10. -/
theorem count_le_from_ten (F : Rectangle)
    (hten : ∀ u forbidden, forbidden ∈ next F u → count F 10 u forbidden ≤ 64)
    (k : ℕ) (hk : 10 ≤ k) (u forbidden : Vertex) (hf : forbidden ∈ next F u) :
    count F k u forbidden ≤ 2 ^ (k-4) := by
  have h := count_growth F 10 64 hten (k-10) u forbidden hf
  rw [Nat.add_sub_of_le hk] at h
  have hp : 2^(k-10) * 64 = 2^(k-4) := by
    change 2^(k-10) * 2^6 = _
    rw [← pow_add]
    congr 1
    omega
  simpa only [hp] using h

end
end RootedKP.RegionalEndpoints
#print axioms RootedKP.RegionalEndpoints.acceptedCount_visited_mono
#print axioms RootedKP.RegionalEndpoints.count_le_from_ten
