import RootedKP.BoundaryCharts
import RootedKP.HoneycombSymmetry
import RootedKP.SideSeparation

/-! Explicit incidence-preserving lattice isometries for the six halo corners. -/
namespace RootedKP.Honeycomb

structure LatticeIso where
  vertex : Vertex ≃ Vertex
  face : Face ≃ Face
  adj_iff : ∀ u v, Adj (vertex u) (vertex v) ↔ Adj u v
  incident_iff : ∀ v f, Incident (vertex v) (face f) ↔ Incident v f

namespace LatticeIso

def identity : LatticeIso :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

def comp (e d : LatticeIso) : LatticeIso where
  vertex := e.vertex.trans d.vertex
  face := e.face.trans d.face
  adj_iff u v := (d.adj_iff _ _).trans (e.adj_iff u v)
  incident_iff v f := (d.incident_iff _ _).trans (e.incident_iff v f)

def translation (dq dr : ℤ) : LatticeIso where
  vertex := {
    toFun := translate dq dr
    invFun := translate (-dq) (-dr)
    left_inv := by intro v; cases v <;> simp [translate]
    right_inv := translate_inverse dq dr }
  face := {
    toFun := fun f => (f.1+dq, f.2+dr)
    invFun := fun f => (f.1-dq, f.2-dr)
    left_inv := by intro f; ext <;> simp
    right_inv := by intro f; ext <;> simp }
  adj_iff := by
    intro u v
    cases u <;> cases v <;> simp [translate, Adj] <;> omega
  incident_iff := by
    intro v f
    cases v <;> rcases f with ⟨q,r⟩ <;> simp [translate, Incident] <;> omega

def rotation : LatticeIso where
  vertex := {
    toFun := rotate
    invFun := fun v => rotate (rotate (rotate (rotate (rotate v))))
    left_inv := rotate_six
    right_inv := rotate_six }
  face := {
    toFun := fun f => (-f.2, f.1+f.2)
    invFun := fun f => (f.1+f.2, -f.1)
    left_inv := by intro f; ext <;> simp
    right_inv := by intro f; ext <;> simp }
  adj_iff := by
    intro u v
    cases u <;> cases v <;> simp [rotate, Adj] <;> omega
  incident_iff := by
    intro v f
    cases v <;> rcases f with ⟨q,r⟩ <;> simp [rotate, Incident] <;> omega

def rotateN : ℕ → LatticeIso
  | 0 => identity
  | n+1 => (rotateN n).comp rotation

end LatticeIso

def chartNextSide (i : Fin 6) : Fin 6 := ⟨(i.val+1)%6, by omega⟩
def chartPrevSide (i : Fin 6) : Fin 6 := ⟨(i.val+5)%6, by omega⟩

/-- Send the adjacent sides i,i+1 to the standard corner q≥0,r≤0. -/
def cornerIso (F : Rectangle) (s : ℕ) (i : Fin 6) : LatticeIso :=
  match i.val with
  | 0 => (LatticeIso.rotateN 2).comp
      (LatticeIso.translation (F.qmax+F.rmax+s) (-(F.qmax+s)))
  | 1 => (LatticeIso.rotateN 1).comp
      (LatticeIso.translation (F.rmax+s) (-(F.qmax+F.rmax+s)))
  | 2 => LatticeIso.translation (-(F.qmin-s)) (-(F.rmax+s))
  | 3 => (LatticeIso.rotateN 5).comp
      (LatticeIso.translation (-(F.qmin+F.rmin-s)) (F.qmin-s))
  | 4 => (LatticeIso.rotateN 4).comp
      (LatticeIso.translation (-(F.rmin-s)) (F.qmin+F.rmin-s))
  | _ => (LatticeIso.rotateN 3).comp
      (LatticeIso.translation (F.qmax+s) (F.rmin-s))

/-- Exact face predicate, with all six corner orientations and translations. -/
theorem cornerIso_face_iff (F : Rectangle) (s : ℕ) (i : Fin 6) (f : Face) :
    BoundaryCharts.FaceIn .corner ((cornerIso F s i).face f) ↔
      0 ≤ sideMargin F s f i ∧ 0 ≤ sideMargin F s f (chartNextSide i) := by
  rcases f with ⟨q,r⟩
  fin_cases i <;>
    simp [cornerIso, LatticeIso.rotateN, LatticeIso.comp, LatticeIso.identity,
      LatticeIso.rotation, LatticeIso.translation, chartNextSide,
      BoundaryCharts.FaceIn, sideMargin] <;> omega

end RootedKP.Honeycomb
#print axioms RootedKP.Honeycomb.cornerIso_face_iff
