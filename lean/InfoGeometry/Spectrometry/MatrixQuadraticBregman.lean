import InfoGeometry.Amari.DuallyFlatThermodynamics
import InfoGeometry.Spectrometry.MatrixFixedScaleLeastSquares

namespace InfoGeometry.Spectrometry.MatrixQuadraticBregman

open scoped BigOperators RealInnerProductSpace
open InfoGeometry.Convex InfoGeometry.Amari.DuallyFlatThermodynamics
open Finset FixedScaleLeastSquares MatrixFixedScaleLeastSquares SvdClrEquivalence

noncomputable section

def squarePotential : ConvexFunctional ℝ where
  F value := value ^ 2
  convex := (show Even (2 : ℕ) by decide).convexOn_pow
  diff := by fun_prop

theorem square_potential_canonical_divergence (first second : ℝ) :
    canonicalDivergence squarePotential first second = (second - first) ^ 2 := by
  have derivative : HasDerivAt squarePotential.F (2 * first) first := by
    simpa [squarePotential] using (hasDerivAt_id first).pow 2
  have gradient_eq : squarePotential.grad first = 2 * first := by
    simpa [ConvexFunctional.grad] using derivative.hasGradientAt.gradient
  rw [canonical_divergence_eq_bregman, gradient_eq]
  simp [squarePotential]
  ring

variable {rowCount acquisitionCount : ℕ}

def entrywiseCanonicalDivergence
    (first second : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ) : ℝ :=
  ∑ row, ∑ acquisition,
    canonicalDivergence squarePotential (first row acquisition) (second row acquisition)

theorem entrywise_canonical_divergence_eq_squared_distance
    (first second : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ) :
    entrywiseCanonicalDivergence first second = matrixSquaredDistance first second := by
  unfold entrywiseCanonicalDivergence matrixSquaredDistance
  apply sum_congr rfl
  intro row _
  apply sum_congr rfl
  intro acquisition _
  rw [square_potential_canonical_divergence, sub_sq_comm]

theorem quadratic_amari_matrix_pythagorean
    (observed : Matrix (Fin rowCount) (Fin acquisitionCount) ℝ)
    (scales : Fin acquisitionCount → ℝ) (profile : Fin rowCount → ℝ)
    (norm_ne : scaleSquareSum scales ≠ 0) :
    entrywiseCanonicalDivergence observed (responseMatrix profile scales) =
      entrywiseCanonicalDivergence observed (reconstruction observed scales) +
        entrywiseCanonicalDivergence (reconstruction observed scales)
          (responseMatrix profile scales) := by
  simp only [entrywise_canonical_divergence_eq_squared_distance]
  exact matrix_projection_pythagorean observed scales profile norm_ne

end

end InfoGeometry.Spectrometry.MatrixQuadraticBregman
