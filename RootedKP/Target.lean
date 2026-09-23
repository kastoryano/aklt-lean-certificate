import RootedKP.Polymers
import RootedKP.HeapQuotient
import RootedKP.RootCounting

/-!
# Exact target statement

This file DEFINES the requested proposition. A definition of a proposition is
not a proof of that proposition. `UniformRootedSummability` is not claimed as
a theorem until the heap, geometry, enumeration and arithmetic bridges have
all been supplied. There are no placeholders or extra axioms here.
-/

namespace RootedKP.AKLT

open scoped BigOperators ENNReal NNReal

abbrev RegionalRootedHeap (F : Honeycomb.Rectangle) :=
  Heaps.AllRootedHeaps (Polymer F) Polymer.Incompatible

noncomputable def rootCutMarks (F : Honeycomb.Rectangle) (cut : Finset Edge)
    (h : RegionalRootedHeap F) : ℕ :=
  cutMarks cut Polymer.edges h.1

/-- Every counted heap has one minimum and that minimum meets the cut. -/
def CutRootedHeap (F : Honeycomb.Rectangle) (cut : Finset Edge) :=
  {h : RegionalRootedHeap F // 0 < rootCutMarks F cut h}

noncomputable def scalarSum (F : Honeycomb.Rectangle) (cut : Finset Edge) : ℝ≥0∞ :=
  ∑' h : CutRootedHeap F cut,
    (rootCutMarks F cut h.val : ℝ≥0∞) *
      (Heaps.Heap.weight Polymer.activity h.val.2.val : ℝ≥0)

/-- The exact uniform scalar conclusion needed by the AKLT response proof.
An extended nonnegative sum bounded by a finite NNReal automatically has a
finite value: convergence cannot disappear behind Lean's convention for an
undefined real-valued infinite sum. -/
def UniformRootedSummability : Prop :=
  ∃ R : ℝ≥0, ∀ (F : Honeycomb.Rectangle) (cut : Finset Edge),
    scalarSum F cut ≤ (cut.card : ℝ≥0∞) * R

noncomputable def rootBudget {F : Honeycomb.Rectangle} (p : Polymer F) : ℝ≥0∞ :=
  ENNReal.ofReal ((p.activity : ℝ) * Real.exp p.cost)

noncomputable def fixedRootMass (F : Honeycomb.Rectangle) (p : Polymer F) : ℝ≥0∞ :=
  ∑' h : Heaps.RootedHeap Polymer.Incompatible p,
    (Heaps.Heap.weight Polymer.activity h.val : ℝ≥0)

/-- The independent uniform root-counting target, with an explicit finite constant. -/
def UniformRootMass : Prop := by
  classical
  exact ∃ R : ℝ≥0, ∀ (F : Honeycomb.Rectangle) (e : Edge),
    (∑' p : Polymer F, if e ∈ p.edges then rootBudget p else 0) ≤ R

/-- The model-specific KP condition, with self-incompatibility included by
the literal vertex-overlap relation. This too is a target, not an axiom. -/
def UniformKPCondition : Prop := by
  classical
  exact ∀ (F : Honeycomb.Rectangle) (p : Polymer F),
    (∑' q : Polymer F,
      if Polymer.Incompatible q p then
        (q.activity : ℝ≥0∞) * ENNReal.ofReal (Real.exp q.cost)
      else 0) ≤ ENNReal.ofReal p.cost

end RootedKP.AKLT
