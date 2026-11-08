import InfoGeometry.Algebra.CuntzComplexStarHomogeneousPositivity

/-!
# Positivity criterion for projection-invariant quotient functionals

Contract: on the owned binary complex-star Cuntz quotient, a complex-linear
functional invariant under the degree-zero projection is positive on all
star-squares exactly when it is positive on core star-squares.
This uses finite homogeneous decomposition and the existing core reduction;
no positivity of the projection is assumed and no completion is introduced.
-/
noncomputable section
namespace InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents

open scoped ComplexOrder
open InfoGeometry.Algebra.CuntzIntegerGrading
open InfoGeometry.Algebra.CuntzComplexStarBinaryGaugeDegreeZero
open InfoGeometry.Algebra.CuntzComplexStarBinaryCoreProjection

theorem projection_invariant_positive_iff (f : Carrier →ₗ[ℂ] ℂ)
    (hinv : ∀ x, f (projection x) = f x) :
    (∀ x, 0 ≤ f (star x * x)) ↔
      ∀ b ∈ core, 0 ≤ f (star b * b) := by
  constructor
  · intro h b _
    exact h b
  · intro hcore x
    rw [← hinv (star x * x), projection_star_mul, map_finsuppSum]
    apply Finset.sum_nonneg
    intro d _
    exact homogeneous_square_nonneg f hcore d (component d x) (delta_component d x)

end InfoGeometry.Algebra.CuntzComplexStarHomogeneousComponents
end
