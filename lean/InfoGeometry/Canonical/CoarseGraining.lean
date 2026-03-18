import InfoGeometry.Canonical.IBFunctional
import Mathlib.Data.Fintype.BigOperators

open MeasureTheory
open scoped BigOperators

namespace InfoGeometry.Canonical

/-!
# Coarse Graining

Canonical coarse-graining interfaces:

- finite retained-state maps with exact fiber summation;
- measure-level encoder marginalization via existing IB machinery.
-/

/-- Finite coarse-graining map from microscopic states to retained macrostates. -/
structure FiniteCoarseGraining (X Y : Type*) where
  project : X → Y

namespace FiniteCoarseGraining

variable {X Y R : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [AddCommMonoid R]

/-- Weight retained on a coarse fiber. -/
def fiberWeight (G : FiniteCoarseGraining X Y) (w : X → R) (y : Y) : R :=
  ∑ x : {x // G.project x = y}, w x

/-- Total microscopic weight before coarse graining. -/
def totalWeight (w : X → R) : R :=
  ∑ x, w x

/-- Exact decomposition of microscopic weight into coarse fibers. -/
theorem totalWeight_eq_sum_fiberWeight
    (G : FiniteCoarseGraining X Y) (w : X → R) :
    totalWeight w = ∑ y, G.fiberWeight w y := by
  simpa [totalWeight, fiberWeight] using (Fintype.sum_fiberwise G.project w).symm

/-- Trivial coarse graining retaining only one macrostate. -/
def trivial (X : Type*) : FiniteCoarseGraining X PUnit where
  project := fun _ => PUnit.unit

/-- Trivial coarse graining keeps the full total weight in its unique fiber. -/
theorem fiberWeight_trivial_eq_totalWeight
    (w : X → R) :
    (trivial X).fiberWeight w PUnit.unit = totalWeight w := by
  simpa [trivial] using (totalWeight_eq_sum_fiberWeight (G := trivial X) w).symm

end FiniteCoarseGraining

section Measure

variable {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]

/-- Measure-level coarse graining by binding a source law through an encoder. -/
noncomputable def encoderMarginal
    [Nonempty T]
    (pX : ProbabilityMeasure X)
    (encoder : X → ProbabilityMeasure T)
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X)) :
    ProbabilityMeasure T :=
  IBFunctional.IBMarginalize pX encoder hae

/-- Coarse-grained encoder marginals are computed by measure bind on fibers. -/
theorem encoderMarginal_apply
    [Nonempty T]
    (pX : ProbabilityMeasure X)
    (encoder : X → ProbabilityMeasure T)
    (hae : AEMeasurable (fun x => (encoder x : Measure T)) (pX : Measure X))
    {s : Set T} (hs : MeasurableSet s) :
    (encoderMarginal pX encoder hae : Measure T) s
      = ∫⁻ x, (encoder x : Measure T) s ∂(pX : Measure X) := by
  simpa [encoderMarginal] using IBFunctional.IBMarginalize_apply
    (pX := pX) (encoder := encoder) (hae := hae) hs

end Measure

end InfoGeometry.Canonical
