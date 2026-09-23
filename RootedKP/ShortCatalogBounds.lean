import RootedKP.ShortLoopRegional
import RootedKP.CompletedLengthCounts

/-! The remaining short-root input is a finite calculation on explicit chart
catalogs. The regional transfer and cumulative comparison are proved below. -/
namespace RootedKP.ShortRootRepresentatives
open Honeycomb AKLT
open scoped BigOperators

def CatalogCumulativeBound (root : Finset Vertex) (cs : List ℕ) : Prop :=
  ∀k : Fin 19,
    (∑i∈Finset.range k.val,catalogCount root (3+i))≤
    ∑i∈Finset.range k.val,cs[i]?.getD 0

/-- All domains are finite and explicitly enumerated. These assertions have
not yet been supplied with numerical proofs. -/
structure ShortCatalogBounds : Prop where
  paths : ∀ell : Fin 3,∀root∈boundaryRootTrails (4+ell.val),
    CatalogCumulativeBound root.toFinset (shortCounts (4+ell.val))
  loops : ∀entry∈loopRootTrails,CatalogCumulativeBound entry.2.toFinset Arithmetic.L6Counts

end RootedKP.ShortRootRepresentatives

namespace RootedKP.AKLT
open Honeycomb ShortRootRepresentatives Arithmetic
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem cumulative_of_catalog {F : Rectangle} (p : Polymer F)
    (root : Finset Vertex) (cs : List ℕ) (hlen : cs.length=18)
    (hc : CatalogCumulativeBound root cs)
    (hfamily : ∀n≤20,∀T : Finset (Polymer F),
      (∀q∈T,q.kind=.path ∧ q.length=n ∧ Polymer.Incompatible p q) →
      T.card≤catalogCount root n) : CumulativePathBound p cs := by
  refine ⟨hlen,?_⟩
  intro k hk
  have hb := hc ⟨k,by omega⟩
  have hh : (∑i∈Finset.range k,pathLengthCount p i)≤
      ∑i∈Finset.range k,catalogCount root (3+i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply hfamily (3+i) (by have := Finset.mem_range.mp hi; omega)
      ((shortPathSet p).filter (fun q => q.length=3+i)) (counted_path_spec p i)
  have hnat : (∑i∈Finset.range k,pathLengthCount p i)≤
      ∑i∈Finset.range k,cs[i]?.getD 0 := hh.trans hb
  unfold prefixSum
  simp only
  exact_mod_cast hnat

theorem short_path_cumulative_of_catalog (H : ShortCatalogBounds)
    {F : Rectangle} (p : Polymer F) (hk : p.kind=.path)
    (hmin : 4≤p.length) (hmax : p.length≤6) :
    CumulativePathBound p (shortCounts p.length) := by
  obtain ⟨root,hr,hfamily⟩ := short_path_root_catalog p hk hmax
  have heq : 4+(p.length-4)=p.length := by omega
  have hc := H.paths ⟨p.length-4,by omega⟩
  simp only [heq] at hc
  apply cumulative_of_catalog p root.toFinset (shortCounts p.length) ?_ (hc root hr) hfamily
  have hcases : p.length=4 ∨ p.length=5 ∨ p.length=6 := by omega
  rcases hcases with h | h | h <;> simp [shortCounts,h,W4Counts,W5Counts,W6Counts]

theorem short_loop_cumulative_of_catalog (H : ShortCatalogBounds)
    {F : Rectangle} (p : Polymer F) (hk : p.kind=.loop) (hmax : p.length≤6) :
    CumulativePathBound p L6Counts := by
  obtain ⟨entry,hr,hfamily⟩ := short_loop_root_catalog p hk hmax
  exact cumulative_of_catalog p entry.2.toFinset L6Counts rfl (H.loops entry hr) hfamily

end
end RootedKP.AKLT
