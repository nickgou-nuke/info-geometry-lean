import InfoGeometry.Canonical.PositiveRayCore
import InfoGeometry.Projective.Bridge
import InfoGeometry.Continuous.PositiveOrthant
import Mathlib.Tactic

/-!
# Expectation-Coordinate Bridge: PositiveRay → Chart Coordinates

This module formalizes the explicit map from quantum projective states (PositiveRay)
to chart coordinates on the positive orthant manifold.

The coordinates are the expectation values of the coordinate observables:
x^μ(q) = ⟨q | X̂^μ | q⟩ = gaugeSection(q)_μ

Since the gauge section provides the normalized density, the coordinates are exactly
the components of this normalized density vector.
-/

noncomputable section

namespace InfoGeometry.Canonical.ExpectationCoordinate

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Projective
open InfoGeometry.Continuous.PositiveOrthant
open InfoGeometry.PositiveMeasure

variable {α : Type*} [Fintype α] [Nonempty α]

/-- 
The expectation-coordinate map:
From a projective positive state (PositiveRay) to chart coordinates on the positive orthant.

For a projective state `q : PositiveRay α`, the coordinate map is:
  x^μ(q) = gaugeSection(q)_μ

This is the expectation value of the coordinate observable X̂^μ in the state q,
where the gauge section provides the normalized density matrix.
-/
noncomputable def expectationCoordinate (q : PositiveRay α) : (α → ℝ) :=
  fun a => gaugeSection (α := α) q a

/-- The coordinate projection map: extracts the μ-th coordinate from a projective state. -/
@[simp]
theorem expectationCoordinate_apply (q : PositiveRay α) (a : α) :
    expectationCoordinate q a = gaugeSection (α := α) q a := rfl

/-- The expectation coordinates are exactly the canonical affine chart
coordinates of the positive projective ray. -/
theorem expectationCoordinate_eq_chartCoordinates (q : PositiveRay α) (a : α) :
    expectationCoordinate q a =
      chartCoordinates (α := α) q a := by
  rfl

/-- The coordinate map lands in the positive orthant chart. -/
noncomputable def expectationPositiveOrthant (q : PositiveRay α) :
    PositiveOrthant α :=
  ⟨WithLp.toLp (2 : ENNReal) (expectationCoordinate q), by
    intro a
    exact (gaugeSection (α := α) q).pos a⟩

@[simp]
theorem expectationPositiveOrthant_coord (q : PositiveRay α) (a : α) :
    coord a (expectationPositiveOrthant q) = expectationCoordinate q a := by
  rfl

theorem expectationPositiveOrthant_eq_chart (q : PositiveRay α) :
    expectationPositiveOrthant q =
      ⟨chartCoordinates (α := α) q, chartCoordinates_pos q⟩ := by
  apply Subtype.ext
  ext a
  rfl

/-- The expectation-coordinate map factors through the gauge section and the Euclidean embedding. -/
theorem expectationCoordinate_eq_gaugeSection_euclidean (q : PositiveRay α) :
    expectationCoordinate q = positiveMeasureToEuclidean (gaugeSection (α := α) q) := by
  funext a
  simp [expectationCoordinate, positiveMeasureToEuclidean_apply, gaugeSection]

/-- The expectation-coordinate map is the composition:
  PositiveRay → (gaugeSection) → PositiveMeasure → (positiveMeasureToEuclidean) → EuclideanSpace ℝ α
This is exactly the map q ↦ ⟨q | X̂^μ | q⟩. -/
theorem expectationCoordinate_factorization (q : PositiveRay α) :
    expectationCoordinate q = (positiveMeasureToEuclidean ∘ gaugeSection (α := α)) q := by
  rw [expectationCoordinate_eq_gaugeSection_euclidean]
  <;> simp [Function.comp_apply]

/-- The expectation-coordinate map lands in the positive orthant cone (all coordinates > 0). -/
theorem expectationCoordinate_pos (q : PositiveRay α) (a : α) :
    0 < expectationCoordinate q a := by
  dsimp [expectationCoordinate, gaugeSection]
  -- The gaugeSection is a PositiveMeasure, so it has a `pos` field proving all coordinates > 0
  exact (gaugeSection (α := α) q).pos a

end InfoGeometry.Canonical.ExpectationCoordinate

end noncomputable section
