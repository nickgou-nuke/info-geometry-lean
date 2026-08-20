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

noncomputable

namespace InfoGeometry.Canonical.ExpectationCoordinate

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Projective
open InfoGeometry.Continuous.PositiveOrthant

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

/-- The expectation-coordinate map lands in the positive orthant. -/
theorem expectationCoordinate_positive (q : PositiveRay α) :
    expectationCoordinate q ∈ positiveOrthantCone α := by
  dsimp [expectationCoordinate, positiveOrthantCone, gaugeSection]
  intro a
  exact (InfoGeometry.Projective.Normalize.normalize_pos (α := α) (Quotient.mk _ (Classical.arbitrary (InfoGeometry.PositiveMeasure α ℝ))) a).trans (by simp)

/-- The expectation-coordinate map as a function to the positive orthant manifold. -/
noncomputable def expectationCoordinateManifold (q : PositiveRay α) : PositiveOrthantManifold α :=
  ⟨expectationCoordinate q, expectationCoordinate_positive q⟩

/-- The coordinate projection map: extracts the μ-th coordinate from a projective state. -/
@[simp]
theorem expectationCoordinate_apply (q : PositiveRay α) (a : α) :
    expectationCoordinate q a = gaugeSection (α := α) q a := rfl

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
  dsimp [expectationCoordinate, gaugeSection] at *
  exact (InfoGeometry.Projective.Normalize.normalize_pos (α := α) (Quotient.mk _ (Classical.arbitrary (InfoGeometry.PositiveMeasure α ℝ))) a).trans (by simp)

/-- The expectation-coordinate map commutes with the cone interior realization. -/
theorem expectationCoordinate_coneInterior (q : PositiveRay α) :
    (expectationCoordinateManifold q : PositiveOrthantManifold α) = (toConeInteriorStateSpace q : PositiveOrthantManifold α) := by
  simp [expectationCoordinateManifold, toConeInteriorStateSpace, expectationCoordinate_factorization]
  <;>
  (try simp_all [PositiveOrthantRaySpace, positiveOrthantCone, positiveOrthant, interior_positiveOrthantCone]) <;>
  (try aesop) <;>
  (try
    {
      ext <;>
      simp_all [expectationCoordinate, gaugeSection, positiveMeasureToEuclidean_apply,
        InfoGeometry.Projective.Normalize.normalizeOnProj_mk] <;>
      aesop
    })

end InfoGeometry.Canonical.ExpectationCoordinate