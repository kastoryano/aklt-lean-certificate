import RootedKP.CachedPathEnumeration
import RootedKP.ShortRootCatalog
namespace RootedKP.CachedPaths
open Honeycomb BoundaryCharts BoundaryCounts Enumeration PackedSupports ShortRootRepresentatives
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def rootMasksFive : List ℕ := [0x2000133,
0x80004f0]
theorem checkFiveA : ∀q : Fin 19,∀r : Fin 18,
    Leaf .corner (Vertex.a ((q.val : ℤ)-2) ((r.val : ℤ)-16)) →
    ∀trail∈extensions (next .corner) 5 [Vertex.a ((q.val : ℤ)-2) ((r.val : ℤ)-16)],
      endsAt (Leaf .corner) trail → pack trail ∈ rootMasksFive := by
  decide +kernel

theorem checkFiveB : ∀q : Fin 19,∀r : Fin 18,
    Leaf .corner (Vertex.b ((q.val : ℤ)-2) ((r.val : ℤ)-16)) →
    ∀trail∈extensions (next .corner) 5 [Vertex.b ((q.val : ℤ)-2) ((r.val : ℤ)-16)],
      endsAt (Leaf .corner) trail → pack trail ∈ rootMasksFive := by
  decide +kernel

theorem coversFive : ∀root∈boundaryRootTrails 5, pack root ∈ rootMasksFive := by
  intro root hr
  obtain ⟨start,hs,he,hstart,hend⟩ := (mem_boundaryRootTrails_iff 5 root).mp hr
  have hb := (mem_anchors start).mp hs
  have hm := (mem_extensions_iff (next .corner) 5 [start] root).mpr he
  cases start with
  | a q r =>
    simp only [qCoord,rCoord] at hb
    have hq : (((q+2).toNat : ℕ) : ℤ)-2=q := by omega
    have hr : (((r+16).toNat : ℕ) : ℤ)-16=r := by omega
    have hh := checkFiveA ⟨(q+2).toNat,by omega⟩
      ⟨(r+16).toNat,by omega⟩
    simp only [hq,hr] at hh
    exact hh hstart root hm hend
  | b q r =>
    simp only [qCoord,rCoord] at hb
    have hq : (((q+2).toNat : ℕ) : ℤ)-2=q := by omega
    have hr : (((r+16).toNat : ℕ) : ℤ)-16=r := by omega
    have hh := checkFiveB ⟨(q+2).toNat,by omega⟩
      ⟨(r+16).toNat,by omega⟩
    simp only [hq,hr] at hh
    exact hh hstart root hm hend
end RootedKP.CachedPaths
