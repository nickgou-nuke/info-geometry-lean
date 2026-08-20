import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Constructions
import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
import InfoGeometry.Projective.Bridge

/-!
# The positive orthant as a concrete smooth chart

The projective positive-ray carrier is not silently given a manifold
structure here.  This file records the genuine finite-dimensional chart
facts used by the continuous information-geometric owners: the strict
positive orthant is an open subset of `EuclideanSpace`, its subtype has the
inherited topology, and the coordinate logarithms are smooth on that open
set.
-/

noncomputable section

namespace InfoGeometry.Continuous.PositiveOrthantChart

open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus
open InfoGeometry.Projective

variable {alpha : Type*} [Fintype alpha]

abbrev Chart (alpha : Type*) := EuclideanSpace Real alpha

/-- The strict positive orthant in the Euclidean chart. -/
def PositiveOrthant : Set (Chart alpha) :=
  interior (positiveOrthantCone (α := alpha) : Set (Chart alpha))

@[simp]
theorem mem_positiveOrthant (x : Chart alpha) :
    x ∈ PositiveOrthant (alpha := alpha) ↔ ∀ i, 0 < x i := by
  exact mem_interior_positiveOrthantCone_iff (α := alpha) x

theorem isOpen_positiveOrthant :
    IsOpen (PositiveOrthant (alpha := alpha)) := by
  exact isOpen_interior

/-- The open-chart subtype carrying the inherited Euclidean topology. -/
abbrev PositiveOrthantManifold :=
  {x : Chart alpha // x ∈ PositiveOrthant (alpha := alpha)}

/-- The canonical inclusion of the chart subtype into its Euclidean carrier. -/
def toAmbient : PositiveOrthantManifold (alpha := alpha) -> Chart alpha :=
  Subtype.val

@[simp]
theorem toAmbient_apply (x : PositiveOrthantManifold (alpha := alpha)) :
    toAmbient (alpha := alpha) x = x.1 := rfl

theorem toAmbient_injective :
    Function.Injective (toAmbient (alpha := alpha)) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem coordinate_positive
    (x : PositiveOrthantManifold (alpha := alpha)) (i : alpha) :
    0 < toAmbient (alpha := alpha) x i := by
  exact (mem_positiveOrthant (alpha := alpha) x.1).1 x.2 i

/-- The coordinate projection is a continuous linear observable on the chart. -/
def projCoord (i : alpha) : Chart alpha →L[ℝ] ℝ :=
  coordinateCLM i

@[simp]
theorem projCoord_apply (i : alpha) (x : Chart alpha) :
    projCoord (alpha := alpha) i x = x i := by
  exact coordinateCLM_apply i x

theorem coordinateLogPotential_contDiffOn
    (i : alpha) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (coordinateLogPotential i)
      (PositiveOrthant (alpha := alpha)) := by
  simpa [PositiveOrthant] using
    InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus.coordinateLogPotential_contDiffOn
      (α := alpha) i

theorem hasFDerivAt_coordinateLogPotential
    (i : alpha) {x : Chart alpha} (hx : x i ≠ 0) :
    HasFDerivAt (coordinateLogPotential i)
      ((1 / x i) • coordinateCLM i) x := by
  exact
    InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus.hasFDerivAt_coordinateLogPotential
      i hx

end InfoGeometry.Continuous.PositiveOrthantChart

end noncomputable section
